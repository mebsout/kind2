(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)


(* Parser for verification problems in the Horn clauses format  
   
   The input problem must be in a (big) monolithic predicate used in exactly
   three clauses (written using SMT-LIB Boolean operators, and explicit
   quantifiers for all variables). The single and only predicate must be named
   {p}:
   
    I(s) => p(s)
    p(s) & T(s, s') => p(s')
    p(s) & !Prop1(s) => false
    ...
    p(s) & !Propn(s) => false


   horn ::= 
   |   (forall (quantified-variables) body) 
   |   (not (exists (quantified-variables) co-body)) 

   body ::= 
   |   (=> co-body body)
   |   (or literal* )
   |   literal

   co-body ::=
   |   (and literal* )
   |   literal

   literal ::=
   |   formula over interpreted relations (such as =, <=, >, ...)
   |   (negated) uninterpreted predicate with arguments

   A body has at most one uninterpreted relation with positive polarity, 
   and a co-body uses only uninterpreted relations with positive polarity.

*)


open Format
open Lib

(* Change this flag to false to deactivate simplifications. Only change it to
   compare results in case an optimization goes wrong. This reverts to
   introducing Skolem for all quantified variables of the Horn clauses. *)
let do_simplify_eqs = true

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module VM = Var.VarMap
module VS = Var.VarSet
module SM = Symbol.SymbolMap

(* Useful HString constants *)

let s_set_info = HString.mk_hstring "set-info"
let s_set_logic = HString.mk_hstring "set-logic"
let s_horn = HString.mk_hstring "HORN"
let s_declare_fun = HString.mk_hstring "declare-fun"
let s_pred = HString.mk_hstring "p"
let s_assert = HString.mk_hstring "assert"
let s_check_sat = HString.mk_hstring "check-sat"

(* Useful term constants *)

let t_int_zero = Term.mk_num_of_int 0
let t_int_one = Term.mk_num_of_int 1
let t_int_minus_one = Term.mk_app Symbol.s_minus [t_int_one]
    
let t_real_zero = Term.mk_dec Decimal.zero
let t_real_one = Term.mk_dec Decimal.one
let t_real_minus_one = Term.mk_app Symbol.s_minus [t_real_one]


module H = Hashcons

module Conv = SMTExpr.Converter (GenericSMTLIBDriver)

let sexpr_conv = GenericSMTLIBDriver.smtlib_string_sexpr_conv
let type_of_sexpr = sexpr_conv.GenericSMTLIBDriver.type_of_sexpr
let expr_of_sexpr = GenericSMTLIBDriver.expr_of_string_sexpr

(* Collect literals from a horn clause body *)
let rec literals_of_body accum = function

  (* All expressions parsed, return *)
  | [] -> accum

  (* Take first expression *)
  | (polarity, expr) :: tl -> match Term.destruct expr with 

    (* Expression is a disjunction in a body or a conjunction in a
       co-body *)
    | Term.T.App (s, l) 
      when 
        (polarity && s == Symbol.s_or) ||
        (not polarity && s == Symbol.s_and) -> 

      (* Parse disjuncts or conjuncts as body or co-body, respectively *)
      literals_of_body 
        accum 
        ((List.map (function d -> (polarity, d)) l) @ tl)

    (* Expression is an implication of arity zero *)
    | Term.T.App (s, []) when polarity && s == Symbol.s_implies -> 

      assert false

    (* Expression is an implication in a body *)
    | Term.T.App (s, l :: r) when polarity && s == Symbol.s_implies -> 

      (* Parse *)
      literals_of_body 
        accum
        ((false, l) :: 
         (polarity, 
          match r with 
            | [] -> assert false 
            | [d] -> d
            | _ -> Term.mk_implies r) :: 
         tl)

    (* Expression is a literal, add to accumulator *)
    | _ -> 

      literals_of_body
        ((if not polarity then Term.negate expr else expr) :: accum) 
        tl


(* Return list of literals of a horn clause *)
let clause_of_expr expr = 

  (* Return a list of temporary variables to instantiate a lambda
     abstraction with *)
  let instantiate_lambda lambda =

    (* Get sorts of binders in lambda abstraction *)
    let sorts = Term.T.sorts_of_lambda lambda in 

    (* For each sort create a temporary variable *)
    let vars = 
      List.map
        (function t -> Term.mk_var (Var.mk_fresh_var t)) 
        sorts 
    in

    (* Instantiate bound variables in lambda abstraction with fresh
       variables *)
    Term.T.instantiate lambda vars 

  in

  (* Get node of term *)
  match Term.T.node_of_t expr with 

    (* Universally quantified expression *)
    | Term.T.Forall l -> 

      (* Instantiate bound variables in lambda abstraction with fresh
         variables *)
      let l' = instantiate_lambda l in

      (* Get literals in body of horn clause *)
      let literals = literals_of_body [] [(true, l')] in

      literals

    (* Negated expression *)
    | Term.T.Node (s, [t]) when s == Symbol.s_not -> 

      (match Term.T.node_of_t t with 

        (* Negated existentially quantified expression *)
        | Term.T.Exists l -> 

          (* Instantiate bound variables in lambda abstraction with fresh
             variables *)
          let l' = instantiate_lambda l in

          (* Get literals in co-body of horn clause *)
          let literals = 
            literals_of_body
              [] 
              [(false, l')]
          in

          literals

        | _ -> 

          raise 
            (Invalid_argument 
               (Format.asprintf 
                  "Expression is not a horn clause: %a"
                  Conv.pp_print_expr expr)))

    | _ -> 

      raise 
        (Invalid_argument 
           (Format.asprintf 
              "Expression is not a horn clause: %a"
              Conv.pp_print_expr expr))

(*

   I(s) => p(s)
   p(s) & T(s, s') => p(s')
   p(s) & !Prop(s) => false

*)

(* Return the polarity of the monolithic predicate in a literal as Some true or
   Some false with the term arguments. If the literal does not contain the
   predicate, return None. *)
let rec polarity_of_pred sym_p polarity expr = match Term.destruct expr with 

  | Term.T.App (s, a) when s == sym_p -> 

    Some (polarity, a)

  | Term.T.App (s, [e]) when s == Symbol.s_not -> 
    polarity_of_pred sym_p (not polarity) e

  | _ -> None


let sym_already_in s l = List.exists (fun (s', _) -> s == s') l

(* Classify a clause, returns lists of positive and negative apperances as well
   as the expression extracted from the horn clause. *)
let classify_clause preds literals =

  List.fold_left 
    (fun (pos, neg, acc) expr -> 

       List.fold_left 
         (fun (pos, neg, acc) sym_p -> 

            (* Get polarity of predicate in literal *)
            match polarity_of_pred sym_p true expr with 
            | Some (true, args) ->

              if sym_already_in sym_p pos then
                raise 
                  (Invalid_argument
                     (Format.asprintf
                        "Predicate %a must occur at most once positvely"
                        Symbol.pp_print_symbol sym_p));

              ((sym_p, args) :: pos, neg, acc)

            | Some (false, args) -> 

              if sym_already_in sym_p neg then
                raise 
                  (Invalid_argument
                     (Format.asprintf
                        "Predicate %a must occur at most once negatively"
                        Symbol.pp_print_symbol sym_p));

              (pos, (sym_p, args) :: neg, acc)

            | None -> (pos, neg, (expr :: acc)))
         
         (pos, neg, acc)
         preds
    )
    ([], [], [])
    literals


(* Return the list of free variables in the term *)
let free_vars_of_term term = 
  Var.VarSet.elements
    (Term.eval_t
       (function 
         | Term.T.Var v when Var.is_free_var v -> 
           (function [] -> Var.VarSet.singleton v | _ -> assert false)
         | Term.T.Var _
         | Term.T.Const _ -> 
           (function [] -> Var.VarSet.empty | _ -> assert false)
         | Term.T.App _ -> List.fold_left Var.VarSet.union Var.VarSet.empty
         | Term.T.Attr (t, _) -> 
           (function [s] -> s | _ -> assert false))
       term)


(* Create a new unique fresh temporary state variable *)
let mk_fresh_state_var =

  let next_fresh_state_var_id = ref 1 in
  fun var_type -> 

  let res = 
    StateVar.mk_state_var 
      (Format.sprintf "I%d" !next_fresh_state_var_id)
      [] var_type
  in

  incr next_fresh_state_var_id;

  res


(* Bind each free variable to a fresh state variable *)
let free_vars_to_state_vars term = 
  let vars = free_vars_of_term term in
  
  let _, sv, svt = 
    List.fold_left
      (fun (i, sv, svt) v ->
         let v = Var.mk_state_var_instance
             (mk_fresh_state_var (Var.type_of_var v))
             Numeral.zero in
         let vt = Term.mk_var v in
         (succ i, v :: sv, vt :: svt))
      (1, [], [])
      vars
  in

  let state_vars, state_var_terms = List.rev sv, List.rev svt in
  
  let t =Term.mk_let 
    (List.combine vars state_var_terms)
    term
  in

  t, state_vars
  

(* Remove let bindings by propagating the values *)
let unlet_term term = Term.construct (Term.eval_t (fun t _ -> t) term)



let rec let_for_args accum = function 

  (* No more terms in list *)
  | [] -> List.rev accum

  (* Term without equations *)
  | (t, []) :: tl ->
    (* Format.eprintf "term wo eq %a @." Term.pp_print_term t; *)
    let_for_args (t :: accum) tl

  (* Add term with let binding to accumulator *)
  | (t, e) :: tl ->
    (* Format.eprintf "term with eq %a, let [%a])@." Term.pp_print_term t
       Term.pp_print_term (Term.mk_let e t); *)
    let_for_args (Term.mk_let e t :: accum) tl

  (* Lists must be of equal length *)
  | _ -> raise (Invalid_argument "let_for_args")



(* Extract the factor and term of a monomial term *)
let extract_monomial t = match Term.destruct t with
  | Term.T.Const _ | Term.T.Var _ ->
    let one =
      match Type.node_of_type (Term.type_of_term t) with
      | Type.Int | Type.IntRange _ -> t_int_one
      | Type.Real -> t_real_one
      | _ -> assert false
    in
    one, t
  | Term.T.App (s, [k; m]) when s == Symbol.s_times -> k, m
  | _ -> assert false 


(* Extract the values of constants with their corresponding terms for a
   polynomial term *)
let extract_polynomial_eq l r =
  assert (Term.equal r t_int_zero || Term.equal r t_real_zero);
  match Term.destruct l with
  | Term.T.App (s, sl) when s == Symbol.s_plus ->
    List.map extract_monomial sl
  | Term.T.Var _ | Term.T.Const _ -> [extract_monomial l]
  | _ -> assert false

(* Reconstruct a term from a polynomial *)
let term_from_poly poly = match poly with
  | [k, _] when Term.equal k t_int_zero -> t_int_zero
  | [k, _] when Term.equal k t_real_zero -> t_real_zero
  | [k, m] when Term.equal k t_int_one || Term.equal k t_real_one -> m
  | [k, m] -> Term.mk_app Symbol.s_times [k; m]
  | _ -> Term.mk_app Symbol.s_plus
          (List.map (fun (k,m) -> Term.mk_app Symbol.s_times [k; m]) poly)


(* Look for the value (if it exists) for a variable v in a polyinomial equation
   of the form 0 = k1 x1 + ... + kv v + ... + kn xn. In this case it returns the
   value (if the coefficient kv of v is non nul)  - k1/kv x1 - ... - kn/kv xn *)
let find_var_value v poly =
  match List.partition (fun (_, m) -> Term.equal m (Term.mk_var v)) poly with
  | [], _ -> None
  | [k, _], [] -> 
    if Term.equal k t_int_zero || Term.equal k t_real_zero then None
    else begin
      match Type.node_of_type (Var.type_of_var v) with
      | Type.Int | Type.IntRange _ -> Some (v, t_int_zero)
      | Type.Real -> Some (v, t_real_zero)
      | _ -> assert false
    end
  | [k, _], r ->
    if Term.equal k t_int_zero || Term.equal k t_real_zero then None
    else
      let rt = term_from_poly r in
      if Term.equal k t_int_minus_one || Term.equal k t_real_minus_one then
        Some (v, rt)
      else if Term.equal k t_int_one then
        Some (v, Simplify.simplify_term []
                (Term.mk_times [t_int_minus_one; rt]))
      else if Term.equal k t_real_one then
        Some (v, Simplify.simplify_term []
                (Term.mk_times [t_real_minus_one; rt]))
      else Some (v, Simplify.simplify_term []
                   (Term.mk_div [k; rt]))
  | _ -> assert false


(* Solve an equation on variable v. Returns None if the equation is not
   solvable otherwise returns a value for v. *)
let solve_eq v teq =
  match Term.destruct (Simplify.simplify_term [] teq) with
  | Term.T.App (s, [l; r]) when s == Symbol.s_eq ->
    let poly = extract_polynomial_eq l r in
    find_var_value v poly
  | _ -> None


(* Try to solve existential variables following an evaluation order which
   contains variables and the term in which they appear, given as argument. *)
let solve_existential_order eval_order =
  let r_subst = 
    List.fold_left (fun subst (v,t) ->
        match solve_eq v t with
        | None -> subst
        | Some sigma -> sigma :: subst
      ) [] eval_order
  in
  List.rev r_subst

(* Remove trivial equations of a term. *)
let remove_trivial_eq term =
  Term.map
    (fun _ t -> match Term.destruct t with
       | Term.T.App (s, [l; r]) when s == Symbol.s_eq && Term.equal l r ->
         Term.t_true
       | Term.T.App (s, [l; r])
         when s == Symbol.s_eq &&
              Term.equal (Simplify.simplify_term [] t) Term.t_true ->
         Term.t_true
       | Term.T.App (s, conj) when s == Symbol.s_and ->
         let changed = ref false in
         let conj' = List.filter (fun t' ->
             if Term.equal t' Term.t_true then (changed := true; false)
             else true
           ) conj in
         if !changed then Term.mk_and conj'
         else t
       | _ -> t
    ) term


(* Cluster let bindings as much as possible to regroup all independant
   bindings. This is done to avoid constructing cascade of lets, which requires
   an expensive renaming de Bruijn indexes each time one binding is added. *)
let cluster_lets l =
  let clusters, last, _ =
    List.fold_left (fun (acc, cluster, currv) (v, t) ->
        let tvs = Term.vars_of_term t in
        if VS.is_empty (VS.inter tvs currv) then
          acc, (v, t) :: cluster, VS.add v currv
        else
          List.rev cluster :: acc, [v, t], VS.empty
      ) ([], [], VS.empty) l
  in
  let clusters = if last = [] then clusters else List.rev last :: clusters in
  List.rev clusters


let pp_order fmt l =
  List.iter (fun (v,t) ->
      fprintf fmt "<- %a [%a] " Var.pp_print_var v Term.pp_print_term t) l;
  fprintf fmt "@."


(* Try to eliminate the existential variable {e} in a subterm {term} where no
   disjunction appear. *)
let elim_in_subterm e term =
  eprintf "elin %a@." pp_order e;
  let t = match e with
    | [] -> term
    | _ ->
      let cls = cluster_lets e in
      List.fold_right (fun cl t -> Term.mk_let cl t) cls term
  in
  Format.eprintf "BEFORE UNLET : %a\n@." Term.pp_print_term t;
  let t = unlet_term t in
  eprintf "  remove trivial@.";
  remove_trivial_eq t


(* Add a dependencies between existential vars found in a subterm. To use with
   Term.eval_t. *)
let add_dep existential_vars term acc =
  match term with
  | Term.T.App (s, _) when s == Symbol.s_eq ->
    let d = List.filter (fun v ->
        Var.VarSet.mem v (Term.vars_of_term (Term.construct term)))
        existential_vars in
    if d = [] then List.concat acc
    else List.concat ([d, Term.construct term] :: acc)
  | Term.T.App (s, _) when s == Symbol.s_and -> List.concat acc
  | _ -> []



(* Printing evaluation orders (just for debugging). *)

let pp_order fmt l =
  List.iter (fun (v,t) ->
      fprintf fmt "<- %a [%a] " Var.pp_print_var v Term.pp_print_term t) l;
  fprintf fmt "@."


let pp_rest fmt l =
  List.iter (fun (d,t) ->
      fprintf fmt "[";
      List.iter (fun v -> fprintf fmt "%a," Var.pp_print_var v) d;
      fprintf fmt "] [[[%a]]]" Term.pp_print_term t;
    ) l;
  fprintf fmt "@."


(* Compute an evaluatuion order thanks to dependencies for eliminating
   existential variables. *)
let dependencies existential_vars term =

  (debug horn "dependencies %a@." Term.pp_print_term term in ());

  (* Compute inter-dependencies between variables. *)
  let d = Term.eval_t (add_dep existential_vars) term in
  (* Partition variables that appear alone (no dependency) from the ones that
     are inter-dependant. *)
  let alone, inter = List.fold_left (fun (alone, inter) -> function
      | [v], t ->
        if List.exists (fun (v', _) -> Var.equal_vars v v') alone then
          alone, inter
        else (v,t) :: alone, inter
      | dt -> alone, dt :: inter) ([], []) d in
  (* Recursively order variables once dependencies can be resolved. The
     parameter last is set to true after one round of postponing to prevent
     infinite recursion. *)
  let rec order r_eval rest postpone last =
    match rest, postpone, last with
    | (d,t) :: r, _, _ ->
      let d' = List.filter (fun v ->
          not (List.exists (fun (v', _) -> Var.equal_vars v v') r_eval)) d in
      begin
        match d' with
        | [] -> order r_eval r postpone last
        | [v] -> order ((v,t) :: r_eval) r postpone last
        | _ -> order r_eval r ((d',t) :: postpone) last
      end
    | [], _::_, false -> order r_eval (List.rev postpone) [] true
    | [], _::_, true ->
      (* Stop there *)
      List.rev r_eval
      (* let evs = *)
      (*   List.fold_left (fun acc (l, _) -> List.rev_append l acc) [] postpone in *)
      (* failwith (asprintf "Could not solve all equations (%a)." *)
      (*             (pp_print_list Var.pp_print_var ", ") evs) *)
    | [], [], _ -> List.rev r_eval
  in

  let eval_order = order alone inter [] false in

  debug horn
    "Evaluation order: %a" pp_order eval_order
  in

  eval_order



(* Push negation under Boolean connectors.

   This is not used anymore because it obfuscate some constructions that are
   useful to remove existential variables. *)
let partial_nnf term =
  let rec nnf positive term =
    match Term.destruct term with
    
    | Term.T.App (s, [t]) when s == Symbol.s_not ->
      nnf (not positive) t

    | Term.T.App (s, l) when s == Symbol.s_and ->
      let l' = List.map (nnf positive) l in
      if positive then Term.mk_and l'
      else Term.mk_or l'

    | Term.T.App (s, l) when s == Symbol.s_or ->
      let l' = List.map (nnf positive) l in
      if positive then Term.mk_or l'
      else Term.mk_and l'

    | Term.T.App (s, i :: r) when s == Symbol.s_implies ->
      let l' = nnf (not positive) i :: (List.map (nnf positive) r) in
      if positive then Term.mk_or l'
      else Term.mk_and l'

    | _ -> if positive then term else Term.negate_simplify term
          
  in
  nnf true term

    
(* Solve (as much as possible) equations that contain existential variables in
   a subterm. *)
let solve_eqs_subterm existential_vars term =
  elim_in_subterm
    (solve_existential_order (dependencies existential_vars term)) term


(* Remove as much existential variables as possible of a subterm by solving its
   equations. *)
let solve_eqs existential_vars term =
  let t =
    Term.eval_t (fun t acc -> match t with
        
        | Term.T.App (s, l) when s == Symbol.s_and ->
          Term.mk_and acc
            
        | Term.T.App (s, l) when s == Symbol.s_or ->
          Term.mk_or (List.map (solve_eqs_subterm existential_vars) acc)
            
        | _ -> Term.construct t) term
  in
  solve_eqs_subterm existential_vars t
 

(* Create a fresh skolem constant. Because Skolems must be new in every state,
   we encode them by state variables. It is important that there exists no
   relation between variables _SKO*.k and _SKO*.(k+1). *)
let fresh_skolem =
  let n = ref 0 in
  fun scope ty ->
    incr n;
    let s = sprintf "_SKO%d" !n in
    StateVar.mk_state_var s scope ty

(* Returns true if a state variable is used to encode a Skolem constant. *)
let is_skolem_statevar v =
  let s = StateVar.string_of_state_var v in
  try String.sub s 0 4 = "_SKO"
  with Invalid_argument _ -> false


(* Skolemize all existential variables that remain in the term. The newly
   introduced Skolem variables are also returned. *)
let skolemize_remaining existential_vars term =
  let vs = Term.vars_of_term term in
  let rem = List.filter (fun v -> VS.mem v vs) existential_vars in
  let skos, b_skos = List.fold_left (fun (skos, bskos) v ->
      let sko = Var.mk_state_var_instance
          (fresh_skolem [] (Var.type_of_var v)) Numeral.zero in
      let skot = Term.mk_var sko in
      sko :: skos, (v, skot) :: bskos
    ) ([], []) rem in
  let t = unlet_term (Term.mk_let b_skos term) in
  t, skos
  


let fresh_prop_name =
  let n = ref 0 in
  fun () ->
    incr n;
    sprintf "P%d" !n




(* Add a Horn clause to the transition system. The first argument is used to
   accumulate inrtoduced Skolem variables, inital conditions, transition
   relations that were found and properties. *)
let add_horn (skolems, init, trans, props)
    literals preds_args pos neg = 

  match pos, neg with 

    | [], [] -> 

      raise 
        (Failure 
           (Format.asprintf 
              "Clause without occurrence of predicate %a"
              HString.pp_print_hstring s_pred))


    (* Predicate occurs only negated: property clause 

       p(s) & !Prop(s) => false 
       p(s) => Prop(s)
    *)
    | [], _ -> 

      (debug horn "add_horn PROP ...@." in ());

      let extra_eqs =
        List.fold_left (fun acc (sym_p, args) ->
            let p_0, _, vars_0, _ = SM.find sym_p preds_args in
            let acc = Term.mk_eq [Term.mk_var p_0; Term.t_true] :: acc in
            List.fold_left2 (fun acc v0 t0 ->
                Term.mk_eq [Term.mk_var v0; t0] :: acc)
              acc vars_0 args
          ) [] neg
      in
      
      let neg_term, existential_vars =
        free_vars_to_state_vars
          (Term.mk_and
             (List.rev_append extra_eqs
                (List.map Term.negate_simplify literals))) in

      (* let neg_term = unlet_term neg_term in *)

      let neg_term' =
        if do_simplify_eqs then solve_eqs existential_vars neg_term
        else neg_term in

      let neg_term', sko_vs = skolemize_remaining existential_vars neg_term' in
      
      let term' = Term.negate neg_term' in

      (debug horn "PROP : %a@." Term.pp_print_term term' in ());
      
      sko_vs @ skolems, init, trans,
      (fresh_prop_name (), TermLib.PropAnnot Lib.dummy_pos, term') :: props


    (* Predicate occurs only positive: initial state constraint

       I(s) => p(s)
    *)
    | _, [] -> 

      (debug horn "add_horn INIT ...@." in ());

      let extra_eqs, vars =
        List.fold_left (fun (acc, vars) (sym_p, args) ->
            let p_0, _, vars_0, _ = SM.find sym_p preds_args in
            let acc = Term.mk_eq [Term.mk_var p_0; Term.t_true] :: acc in
            List.fold_left2
              (fun acc v0 t0 -> Term.mk_eq [Term.mk_var v0; t0] :: acc)
              acc vars_0 args,
            List.rev_append (p_0 :: vars_0) vars
          ) ([], []) pos
      in
      let vars = List.rev vars in
      
      let term, existential_vars =
        free_vars_to_state_vars
          (Term.mk_and
             (List.rev_append extra_eqs
                (List.map Term.negate_simplify literals))) in
      
      (* let term = unlet_term term in *)

      let term' =
        if do_simplify_eqs then solve_eqs existential_vars term
        else term in

      let term', sko_vs = skolemize_remaining existential_vars term' in

      (debug horn "INIT : %a@." Term.pp_print_term term' in ());

      sko_vs @ skolems, (term', sko_vs, vars) :: init, trans, props


    (* Predicate occurs positive and negative: transition relation

        p(s) & T(s, s') => p(s')
    *)
    | _, _ -> 

      (debug horn "add_horn TRANS ...@." in ());

      let extra_eqs, vars =
        List.fold_left (fun (acc, vars) (sym_p, args) ->
            let p_0, _, vars_0, _ = SM.find sym_p preds_args in
            let acc = Term.mk_eq [Term.mk_var p_0; Term.t_true] :: acc in
            List.fold_left2
              (fun acc v0 t0 -> Term.mk_eq [Term.mk_var v0; t0] :: acc)
              acc vars_0 args,
            List.rev_append (p_0 :: vars_0) vars
          ) ([], []) neg
      in

      let extra_eqs, vars =
        List.fold_left (fun (acc, vars) (sym_p, args) ->
            let _, p_1, _, vars_1 = SM.find sym_p preds_args in
            let acc = Term.mk_eq [Term.mk_var p_1; Term.t_true] :: acc in
            List.fold_left2
              (fun acc v1 t1 -> Term.mk_eq [Term.mk_var v1; t1] :: acc)
              acc vars_1 args,
            List.rev_append (p_1 :: vars_1) vars
          ) (extra_eqs, vars) pos
      in

      let vars = List.rev vars in

      let term, existential_vars =
        free_vars_to_state_vars
          (Term.mk_and
             (List.rev_append extra_eqs
                (List.map Term.negate_simplify literals))) in

      (* let term = unlet_term term in *)

      let term' =
        if do_simplify_eqs then solve_eqs existential_vars term
        else term in

      let term', sko_vs = skolemize_remaining existential_vars term' in

      (debug horn "TRANS : %a@." Term.pp_print_term term' in ());
      
      sko_vs @ skolems, init, (term', sko_vs, vars) :: trans, props



(* Parse a Horn clauses problem expressed as a monolithic system. *)
let rec parse acc preds_args lexbuf = 

  (* Parse S-expression *)
  match  SExprParser.sexp_opt SExprLexer.main lexbuf with 

  | None ->
    (match acc with
     (* Construct transition system from gathered information *)
     | sko_vars, inits, rules, props ->

       let state_vars_set = SM.fold (fun _ (p_0, _, vars_0, _) acc ->
           List.fold_left (fun acc e ->
               SVS.add (Var.state_var_of_state_var_instance e) acc
             ) acc (p_0 :: vars_0)
         ) preds_args SVS.empty in

       let state_vars = SVS.elements state_vars_set in

       let init_vars, init_disj =
         List.fold_left (fun (allvars, disj) (term, skos, vars) ->
             (skos @ vars @ allvars), (term :: disj)
           ) ([], []) inits in

       let init_t = Term.mk_or init_disj in
       let init_sig = List.map Var.type_of_var init_vars in
       (* Symbol for initial state constraint for node *)
       let init_uf_symbol = UfSymbol.mk_uf_symbol
           LustreIdent.init_uf_string init_sig Type.t_bool in

       let pred_def_init = 
         init_uf_symbol,
         ((* Init flag *)
           [ TransSys.init_flag_var TransSys.init_base ] @
           init_vars,
           (* Add constraint for init flag to be true *)
           Term.mk_and 
             [TransSys.init_flag_var TransSys.init_base |> Term.mk_var;
              init_t]
         )
       in

       let trans_vars, trans_disj =
         List.fold_left (fun (allvars, disj) (term, skos, vars) ->
             (skos @ vars @ allvars), (term :: disj)
           ) ([], []) rules in

       let trans_t = Term.mk_or trans_disj in
       let trans_sig = List.map Var.type_of_var trans_vars in
       (* Symbol for transial state constraint for node *)
       let trans_uf_symbol = UfSymbol.mk_uf_symbol
           LustreIdent.trans_uf_string trans_sig Type.t_bool in

       let pred_def_trans = 
         (trans_uf_symbol,
          ((* Init flag. *)
            [ TransSys.init_flag_var TransSys.trans_base ] @
            trans_vars,
            (* Add constraint for init flag to be false *)
            Term.mk_and
              [TransSys.init_flag_var TransSys.trans_base
               |> Term.mk_var |> Term.mk_not;
               trans_t ]
          ))
       in

       let sko_st = List.map Var.state_var_of_state_var_instance sko_vars in
       
       TransSys.mk_trans_sys [] (* scope *) (state_vars @ sko_st)
         pred_def_init pred_def_trans [] (List.rev props) TransSys.Horn
         
     | _ -> assert false)
    
  | Some s -> match s with 

    (* (set-info ...) *)
    | HStringSExpr.List (HStringSExpr.Atom s :: _) when s == s_set_info -> 

      (* Skip *)
      parse acc preds_args lexbuf

    (* (set-logic HORN) *)
    | HStringSExpr.List [HStringSExpr.Atom s; HStringSExpr.Atom l]
      when s == s_set_logic && l == s_horn -> 

      (* Skip *)
      parse acc preds_args lexbuf

    (* (set-logic ...) *)
    | HStringSExpr.List [HStringSExpr.Atom s; e] when s == s_set_logic -> 

      raise 
        (Failure 
           (Format.asprintf 
              "@[<hv>Invalid logic %a, must be HORN" 
              HStringSExpr.pp_print_sexpr e))

    (* Predicate declaration (declare-fun p a r) *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; 
         HStringSExpr.Atom p; 
         HStringSExpr.List a; 
         (HStringSExpr.Atom _ as r)]
      when s == s_declare_fun  -> 

      (* Types of argument of monolithic predicate *)
      let arg_types = List.map type_of_sexpr a in

      (* Types of result of monolithic predicate *)
      let res_type = type_of_sexpr r in

      let p_name = HString.string_of_hstring p in
      
      (* Declare predicate *)
      let sym_p = 
        Symbol.mk_symbol (`UF (UfSymbol.mk_uf_symbol p_name arg_types res_type))
      in

      (* Create a state variable for the value of p *)
      let sv_p = StateVar.mk_state_var p_name ["predicate"] res_type in
      let p_0 = Var.mk_state_var_instance sv_p Numeral.zero in
      let p_1 = Var.mk_state_var_instance sv_p Numeral.one in

      (* Create a state variables for the arguments of p *)
      let _, rvars_0, rvars_1 =
        List.fold_left 
          (fun (i, vars_0, vars_1) t -> 

             let sv = StateVar.mk_state_var (string_of_int i) [p_name] t in

             (succ i, 
              (Var.mk_state_var_instance sv Numeral.zero) :: vars_0, 
              (Var.mk_state_var_instance sv Numeral.one) :: vars_1))
          (1, [], [])
          arg_types
      in
      let vars_0, vars_1 = List.rev rvars_0, List.rev rvars_1 in
      
      (* Continue *)
      parse acc (SM.add sym_p (p_0, p_1, vars_0, vars_1) preds_args) lexbuf

    (* Horn clause: (assert ...) *)
    | HStringSExpr.List [HStringSExpr.Atom s; e] when s == s_assert -> 

      if SM.is_empty preds_args then raise (Failure "No predicates declared");
      let expr = expr_of_sexpr e in

      (* Clausify at top level *)
      let clause = clause_of_expr expr in

      let sym_preds = List.map fst (SM.bindings preds_args) in

      (* Indentify state variables and classify clauses based on the polarity
         of the predicate {p} *)
      let pos, neg, clause' = classify_clause sym_preds clause in

      (* Construct kind2 formulas from this horn clause *)
      let acc = add_horn acc clause' preds_args pos neg in

      (* Continue *)
      parse acc preds_args lexbuf


    (* (check-sat) *)
    | HStringSExpr.List [HStringSExpr.Atom s] when s == s_check_sat -> 

      (* Skip *)
      parse acc preds_args lexbuf

    | e -> 

      raise 
        (Failure 
           (Format.asprintf 
              "@[<hv>Unexpected S-expression@ @[<hv 1>%a@]@]" 
              HStringSExpr.pp_print_sexpr e))




(* Parse SMTLIB2 Horn format from channel. The input problem must be in a (big)
   monolithic predicate used in exactly 3 Horn Clauses. *)
let of_channel in_ch =   

  (* Initialise buffer for lexing *)
  let lexbuf = Lexing.from_channel in_ch in

  parse ([], [], [], []) SM.empty lexbuf




(* Parse SMTLIB2 Horn format from file and construct an internal transition
   system. *)
let of_file filename = 

  (* Open the given file for reading *)
  let use_file = open_in filename in
  let in_ch = use_file in

  let transSys = of_channel in_ch in

  debug horn
     "%a"
     TransSys.pp_print_trans_sys transSys
  in

  transSys



(* ************************************************************ *)
(* Counterexample output in plain text                          *)
(* ************************************************************ *)


let print_term_or_lambda fmt = function
  | Model.Term t -> Term.pp_print_term fmt t
  | Model.Lambda l -> Term.pp_print_lambda fmt l

(* Return width of widest identifier and widest value *)
let rec widths_of_model max_ident_width max_val_width = function 
  
  | [] -> (max_ident_width, max_val_width)

  | (state_var, values) :: tl -> 

    (* Maximal print width of state variable *)
    let max_ident_width' = 
      max
        max_ident_width
        (String.length 
           (string_of_t StateVar.pp_print_state_var state_var))
    in
    
    (* Maximal print width of values *)
    let max_val_width' =
      List.fold_left 
        (fun m v -> 
           max
             m
             (String.length
                (string_of_t print_term_or_lambda v)))
        max_val_width
        values
    in

    (* Return new maximum widths *)
    widths_of_model max_ident_width' max_val_width' tl

(* Pretty-print a value in a model *)
let pp_print_value_pt val_width ppf value = 

  Format.fprintf
    ppf
    "%-*s"
    val_width
    (string_of_t print_term_or_lambda value)

(* Pretty-print a state variable and its values *)
let pp_print_state_var_pt state_var_width val_width ppf (state_var, values) =

  Format.fprintf 
    ppf
    "@[<h>%-*s: %a@]"
    state_var_width
    (string_of_t StateVar.pp_print_state_var state_var)
    (pp_print_list
       (pp_print_value_pt val_width)
       " ")
    values


let filter_out_skolems model =
  List.filter (fun (v, _) -> not (is_skolem_statevar v)) model

(* Pretty-print a model without the values for the Skolem variables. Because
   they are not original state variables, their values are generally not
   useful. *)
let pp_print_path_pt ppf model = 
  let model = filter_out_skolems model in
  let state_var_width, val_width = widths_of_model 0 0 model in

  Format.fprintf
    ppf
    "@[<v>%a@]"
    (pp_print_list
       (pp_print_state_var_pt state_var_width val_width)
       "@,")
    model
       


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
