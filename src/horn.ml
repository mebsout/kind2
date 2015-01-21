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

open Lib
open Format

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module VM = Var.VarMap
  
module Conv = SMTExpr.Converter (Z3Driver)

let s_set_info = HString.mk_hstring "set-info"

let s_set_logic = HString.mk_hstring "set-logic"

let s_horn = HString.mk_hstring "HORN"

let s_declare_fun = HString.mk_hstring "declare-fun"

let s_pred = HString.mk_hstring "p"

let s_assert = HString.mk_hstring "assert"

let s_check_sat = HString.mk_hstring "check-sat"

(*

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

module H = Hashcons


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

(* Return the polarity of the monolithic predicate in a literal as
   Some true ot Some false. If the literal does not contain the
   predicate, return None. *)
let rec polarity_of_pred sym_p polarity expr = match Term.destruct expr with 

  | Term.T.App (s, a) when s == sym_p -> 

    Some 
      (polarity, 

       (* Extract variables from arguments to predicate *)
       List.map 
         (function t -> match Term.destruct t with 
            | Term.T.Var v -> v
            | _ ->
              raise 
                (Invalid_argument "Arguments of predicate must be variables.")
         ) a
      )

  | Term.T.App (s, [e]) when s == Symbol.s_not -> 
    polarity_of_pred sym_p (not polarity) e

  | _ -> None


(* Classify a clause, return a pair of Booleans indicating whether the
   clause contains the monolithic predicate with positive or negative
   polarity, respectively *)
let classify_clause sym_p literals =

  List.fold_left 
    (fun (pos, neg, accum) expr -> 

       (* Get polarity of predicate in literal *)
       match polarity_of_pred sym_p true expr with 
         | Some (true, args) -> 

           if pos = [] then (args, neg, accum) else

             raise 
               (Invalid_argument 
                  "Predicate must occur at most once positvely")

         | Some (false, args) -> 
           
           if neg = [] then (pos, args, accum) else 

             raise 
               (Invalid_argument 
                  "Predicate must occur at most once positvely")

         | None -> (pos, neg, (expr :: accum)))

    ([], [], [])
    literals


(* Return the list of temporary variables in the term *)
let temp_vars_of_term term = 

  Var.VarSet.elements
    (Term.eval_t
       (function 
         | Term.T.Var v when Var.is_temp_var v -> 
           (function [] -> Var.VarSet.singleton v | _ -> assert false)
         | Term.T.Var _
         | Term.T.Const _ -> 
           (function [] -> Var.VarSet.empty | _ -> assert false)
         | Term.T.App _ -> List.fold_left Var.VarSet.union Var.VarSet.empty
         | Term.T.Attr (t, _) -> 
           (function [s] -> s | _ -> assert false))
       term)
    

(* Bind each temporary variable to a fresh constant *)
let temp_vars_to_consts term = 

  let vars = temp_vars_of_term term in

  let consts = 
    List.map
      (function v -> 
        Term.mk_uf (UfSymbol.mk_fresh_uf_symbol [] (Var.type_of_var v)) [])
      vars
  in

  Term.mk_let 
    (List.combine vars consts)
    term


let next_fresh_state_var_id = ref 1

let mk_fresh_state_var scope var_type = 

  let res = 
    StateVar.mk_state_var 
      (Format.sprintf "I%d" !next_fresh_state_var_id)
      scope
      var_type
  in

  incr next_fresh_state_var_id;

  res


(* Bind each temporary variable to a fresh state variable *)
let temp_vars_to_state_vars scope term = 
  (* Format.eprintf "TEMP VARS TERM : %a@." Term.pp_print_term term; *)
  let vars = temp_vars_of_term term in
  (* List.iter (Format.eprintf "TEMP VARS = %a@." Var.pp_print_var) vars; *)
  
  let _, sv, svt = 
    List.fold_left
      (fun (i, sv, svt) v ->
         let v = Var.mk_state_var_instance
             (mk_fresh_state_var scope (Var.type_of_var v))
             Numeral.zero in
         let vt = Term.mk_var v in
         (succ i, v :: sv, vt :: svt))
      (1, [], [])
      vars
  in

  let state_vars, state_var_terms = List.rev sv, List.rev svt in
  (* List.iter (Format.eprintf "new TEMP VARS = %a@." Var.pp_print_var) state_vars; *)
  
  let t =Term.mk_let 
    (List.combine vars state_var_terms)
    term
  in
  (* Format.eprintf "RES TEMP VARS : %a@." Term.pp_print_term t; *)
  t, state_vars
  

let unlet_term term = Term.construct (Term.eval_t (fun t _ -> t) term)

(*

   I(s) => p(s)
   p(s) & T(s, s') => p(s')
   p(s) & !Prop(s) => false

*)



let rec let_for_args accum = function 

  (* No more terms in list *)
  | [] -> List.rev accum

  (* Term without equations *)
  | (t, []) :: tl ->
    (* Format.eprintf "term wo eq %a @." Term.pp_print_term t; *)
    let_for_args (t :: accum) tl

  (* Add term with let binding to accumulator *)
  | (t, e) :: tl ->
    (* Format.eprintf "term with eq %a, let [%a])@." Term.pp_print_term t Term.pp_print_term (Term.mk_let e t); *)
    let_for_args (Term.mk_let e t :: accum) tl

  (* Lists must be of equal length *)
  | _ -> raise (Invalid_argument "let_for_args")



let t_int_zero = Term.mk_num_of_int 0
let t_int_one = Term.mk_num_of_int 1
let t_int_minus_one = Term.mk_app Symbol.s_minus [t_int_one]
    
let t_real_zero = Term.mk_dec Decimal.zero
let t_real_one = Term.mk_dec Decimal.one
let t_real_minus_one = Term.mk_app Symbol.s_minus [t_real_one]


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


let extract_polynomial_eq l r =
  assert (Term.equal r t_int_zero || Term.equal r t_real_zero);
  match Term.destruct l with
  | Term.T.App (s, sl) when s == Symbol.s_plus ->
    List.map extract_monomial sl
  | _ -> assert false

let term_from_poly poly = match poly with
  | [k, _] when Term.equal k t_int_zero -> t_int_zero
  | [k, _] when Term.equal k t_real_zero -> t_real_zero
  | [k, m] when Term.equal k t_int_one || Term.equal k t_real_one -> m
  | [k, m] -> Term.mk_app Symbol.s_times [k; m]
  | _ -> Term.mk_app Symbol.s_plus
          (List.map (fun (k,m) -> Term.mk_app Symbol.s_times [k; m]) poly)

let find_var_value v poly =
  match List.partition (fun (_, m) -> Term.equal m (Term.mk_var v)) poly with
  | [], _ -> None
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


let solve_eq v teq =
  match Term.destruct (Simplify.simplify_term [] teq) with
  | Term.T.App (s, [l; r]) when s == Symbol.s_eq ->
    let poly = extract_polynomial_eq l r in
    find_var_value v poly
  | _ -> None


let already_in_subst v =
  List.exists (List.exists (fun (v', _) -> Var.equal_vars v v'))


let solve_existential existential_vars term acc =  match term with
  | Term.T.App (s, [l; r]) when s == Symbol.s_eq ->
    let subst =
      List.fold_left (fun subst v ->
          if already_in_subst v (subst :: acc) then subst
          else
            match solve_eq v (Term.construct term) with
            | None -> subst
            | Some sigma -> sigma :: subst
        ) [] existential_vars in
    List.concat (subst :: acc)

  | Term.T.App (s, l) when s == Symbol.s_and -> List.concat acc

  | Term.T.App (s, l) -> List.concat acc

  | Term.T.Const _ | Term.T.Var _ -> []

  | Term.T.Attr (t, _) -> List.concat acc


let solve_existential_order eval_order =
  let r_subst = 
    List.fold_left (fun subst (v,t) ->
        match solve_eq v t with
        | None -> subst
        | Some sigma -> sigma :: subst
      ) [] eval_order
  in
  List.rev r_subst


let add_dep existential_vars term acc = match term with
  | Term.T.App (s, [l; r]) when s == Symbol.s_eq ->
    let d = List.filter (fun v ->
        Var.VarSet.mem v (Term.vars_of_term (Term.construct term)))
        existential_vars in
    if d = [] then List.concat acc
    else List.concat ([d, Term.construct term] :: acc)
  | _ -> List.concat acc


(* let pp_order fmt l = *)
(*   List.iter (fun (v,t) -> *)
(*       fprintf fmt "<- %a [%a] " Var.pp_print_var v Term.pp_print_term t) l; *)
(*   fprintf fmt "@." *)


(* let pp_rest fmt l = *)
(*   List.iter (fun (d,t) -> *)
(*       fprintf fmt "["; *)
(*       List.iter (fun v -> fprintf fmt "%a," Var.pp_print_var v) d; *)
(*       fprintf fmt "] [[[%a]]]" Term.pp_print_term t; *)
(*     ) l; *)
(*   fprintf fmt "@." *)

let dependencies existential_vars term = 
  let d = Term.eval_t (add_dep existential_vars) term in
  let alone, inter = List.fold_left (fun (alone, inter) -> function
      | [v], t ->
        if List.exists (fun (v', _) -> Var.equal_vars v v') alone then
          alone, inter
        else (v,t) :: alone, inter
      | dt -> alone, dt :: inter) ([], []) d in
  (* eprintf "ALONE : %a" pp_order alone; *)
  let rec order r_eval rest postpone =
    (* eprintf "ORDER : %a" pp_order r_eval; *)
    (* eprintf "REST : %a" pp_rest rest; *)
    (* eprintf "POSTPONE : %a" pp_rest postpone; *)
    match rest, postpone with
    | (d,t) :: r, _ ->
      let d' = List.filter (fun v ->
          not (List.exists (fun (v', _) -> Var.equal_vars v v') r_eval)) d in
      begin
        match d' with
        | [] -> order r_eval r postpone
        | [v] -> order ((v,t) :: r_eval) r postpone
        | _ -> order r_eval r ((d',t) :: postpone)
      end
    | [], _::_ -> order r_eval postpone []
    | [], [] -> List.rev r_eval
  in
  order alone inter []


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
  

let solve_eqs existential_vars term =
  (* unlet_term *)
    let t = (match Term.eval_t (solve_existential existential_vars) term with
      | [] -> term
      | e ->
        (* List.iter (fun (v,t) -> *)
        (*     Format.eprintf "BINDINGS : %a -> %a\n@." Var.pp_print_var v Term.pp_print_term t) e; *)
        List.fold_right (fun b t -> Term.mk_let [b] t) e term)
    in
    (* Format.eprintf "BEFORE UNLET : %a\n@." Term.pp_print_term t; *)
    unlet_term t

let solve_eqs existential_vars term =
  let t =
    match solve_existential_order (dependencies existential_vars term) with
    | [] -> term
    | e ->
      (* List.iter (fun (v,t) -> *)
      (*     Format.eprintf "BINDINGS : %a -> %a\n@." Var.pp_print_var v Term.pp_print_term t) e; *)
      List.fold_right (fun b t -> Term.mk_let [b] t) e term
  in
  (* Format.eprintf "BEFORE UNLET : %a\n@." Term.pp_print_term t; *)
  let t = unlet_term t in
  remove_trivial_eq t


let eq_to_let state_vars term accum = match term with

  (* An equation *)
  | Term.T.App (s, [l; r]) when s == Symbol.s_eq -> 

    (* Match left-hand side and right-hand side of equation *)
    (match Term.destruct l, Term.destruct r with

      (* Equation between state variable and free variable *)
      | Term.T.Var v1, Term.T.Var v2 when 
          SVS.mem 
            (Var.state_var_of_state_var_instance v1) 
            state_vars && 
          (not 
             (SVS.mem
                (Var.state_var_of_state_var_instance v2) 
                state_vars)) -> 
        
        (* Initialize accumulator with single equation, binding the
           free variable to the state variable *)
        (Term.construct term, [(v2, Term.mk_var v1)])

      (* Equation between state variable and free variable *)
      | Term.T.Var v1, Term.T.Var v2 when 
          SVS.mem
            (Var.state_var_of_state_var_instance v2)
            state_vars
          && 
          (not
             (SVS.mem
                (Var.state_var_of_state_var_instance v1)
                state_vars)) -> 
        
        (* Initialize accumulator with single equation, binding the
           free variable to the state variable *)
        (Term.construct term, [(v1, Term.mk_var v2)])
        

      | _ ->

        (* Other equation, add let binding for collected equations *)
        
        (* Format.eprintf "lfa accum = %d@." (List.length accum); *)
        (* List.iter (fun (t, e) -> Format.eprintf "%a@." Term.pp_print_term (Term.mk_let e t)) accum; *)
        (Term.mk_eq (let_for_args [] accum), [])
        
    )

  (* Conjunction, can join equations from all conjuncts *)
  | Term.T.App (s, l) when s == Symbol.s_and -> 

    (* Keep term unchanged and concatenate lists of equations *)
    (Term.mk_and (List.map fst accum),
     List.concat (List.map snd accum))

  (* Neither conjunction nor equation, add respective collected
     equations as let binding to each subterm *)
  | Term.T.App (s, l) -> (Term.mk_app s (let_for_args [] accum), [])

  (* No equations for constants and variables *)
  | Term.T.Const s -> (Term.mk_const s, [])
  | Term.T.Var v -> (Term.mk_var v, [])

  (* Remove attributed terms *)
  | Term.T.Attr (t, _) -> (t, snd (List.hd accum))


let solve_eqs_old state_vars term =

  let t =   (* unlet_term *)
    (match Term.eval_t (eq_to_let state_vars) term with
     | t, [] -> t
     | t, e -> Term.mk_let e t)
  in
  (* Format.eprintf "BEFORE UNLET : %a\n@." Term.pp_print_term t; *)
  unlet_term t



(* let rec look_for_eq v = function *)
(*   | Term.T.App (s, l) when s == Symbol.s_and -> *)
    


(* let elim_existential_var v state_vars term = *)

(*   assert false *)
  


let add_horn (init, trans, props) scope
    literals vars_0 vars_1 var_pos var_neg = 
  
  let state_vars = 
    List.fold_left
      (fun a e -> SVS.add (Var.state_var_of_state_var_instance e) a)
      SVS.empty vars_0
  in

  match var_pos, var_neg with 

    | [], [] -> 

      raise 
        (Failure 
           (Format.asprintf 
              "Clause without occurrence of predicate %a"
              HString.pp_print_hstring s_pred))


    (* Predicate occurs only negated: property clause 

       p(s) & !Prop(s) => false

    *)
    | [], _ -> 

      let term, existential_vars =
        temp_vars_to_state_vars
          scope
          (Term.mk_let 
             (List.combine var_neg (List.map Term.mk_var vars_0))
             (Term.negate (Term.mk_and (List.map Term.negate literals)))) in
      (* (Term.mk_or literals))) *)
      
      let term = unlet_term term in

      (* Format.eprintf "PROP : %a@." Term.pp_print_term term; *)
      let term' = if true then solve_eqs existential_vars term else term in
      (* let term' = if true then solve_eqs_old state_vars term else term in *)
      (* Format.eprintf "PROP afeter solver : %a@." Term.pp_print_term term'; *)
      
      init, trans,
      ("P", TermLib.PropAnnot Lib.dummy_pos, term') :: props


    (* Predicate occurs only positive: initial state constraint

       I(s) => p(s)
       
    *)
    | _, [] -> 

      let term, existential_vars =
        temp_vars_to_state_vars
          scope
          (Term.mk_let 
             (List.combine var_pos (List.map Term.mk_var vars_0))
             (Term.mk_and (List.map Term.negate_simplify literals)))
      in
      
      let term = unlet_term term in

      (* Format.eprintf "INIT : %a@." Term.pp_print_term term; *)
      (* Format.eprintf "INIT SIMPLIFIED  : %a@." Term.pp_print_term (Simplify.simplify_term [] term); *)
      let term' = if true then solve_eqs existential_vars term else term in
      (* let term' = if true then solve_eqs_old state_vars term else term in *)
      (* Format.eprintf "INIT afeter solver : %a@." Term.pp_print_term term'; *)
      (* Format.eprintf "INIT SIMPLIFIED  : %a@." Term.pp_print_term (Simplify.simplify_term [] term'); *)

      (* Symbol for initial state constraint for node *)
      let init_uf_symbol = 
        UfSymbol.mk_uf_symbol
          (* Name of symbol *)
          LustreIdent.init_uf_string
          (* Types of variables in the signature *)
          (List.map Var.type_of_var var_pos)
          (* Symbol is a predicate *)
          Type.t_bool
      in

      let pred_def_init = 
        (* Name of symbol *)
        (init_uf_symbol,
         ((* Init flag? *)
           [ TransSys.init_flag_var TransSys.init_base ] @
           vars_0,
           (* Add constraint for init flag to be true *)
           Term.mk_and 
             [TransSys.init_flag_var TransSys.init_base |> Term.mk_var;
              term']
         ))
      in
      
      pred_def_init :: init, trans, props


    (* Predicate occurs positive and negative: transition relation

        p(s) & T(s, s') => p(s')
       
    *)
    | _, _ -> 

      let term, existential_vars =
        temp_vars_to_state_vars
          scope
          (Term.mk_let 
             (List.combine var_neg (List.map Term.mk_var vars_0))
             (Term.mk_let 
                (List.combine var_pos (List.map Term.mk_var vars_1))
                (Term.mk_and (List.map Term.negate_simplify literals))))
      in

      let term = unlet_term term in

      let term' = if true then solve_eqs existential_vars term else term in
      (* let term' = if true then solve_eqs_old state_vars term else term in *)


      (* Symbol for transition relation for node *)
      let trans_uf_symbol = 
        UfSymbol.mk_uf_symbol
          (* Name of symbol *)
          LustreIdent.trans_uf_string
          (* Types of variables in the signature *)
          (List.map Var.type_of_var (var_neg @ var_pos))
          (* Symbol is a predicate *)
          Type.t_bool
      in

      let pred_def_trans = 
        (trans_uf_symbol,
         ((* Init flag. *)
           [ TransSys.init_flag_var TransSys.trans_base ] @
           vars_0 @ vars_1,

           (* Add constraint for init flag to be false *)
           Term.mk_and
             [TransSys.init_flag_var TransSys.trans_base
              |> Term.mk_var |> Term.mk_not;
              term']
         ))
      in

      init, pred_def_trans :: trans, props


(* type current_subrange = *)
(*     Sub_Empty | Sub_Omega | Sub_Range of Numeral.t * Numeral.t *)


(* let find_trivial_subranges state_vars init trans = *)
(*   let all_empty = *)
(*     List.fold_left (fun acc sv -> *)
(*         if Type.equal_types Type.Int (StateVar.type_of_state_var sv) then *)
(*           SVM.add sv Sub_Empty acc *)
(*         else acc *)
(*       ) SVM.empty state_vars in *)

(*   let adasdiojfiow = *)
(*     Term.eval_t *)

let rec parse acc sym_p_opt lexbuf = 

  (* Parse S-expression *)
  match  SExprParser.sexp_opt SExprLexer.main lexbuf with 

  | None ->
    (match acc with
     (* Construct transition system from gathered information *)
     | [init], [trans], props ->
       
       let state_vars = match sym_p_opt with
         | None -> []
         | Some (_, vars, _) ->
           let svs = List.fold_left
             (fun a e -> SVS.add e a)
             SVS.empty
             (List.map Var.state_var_of_state_var_instance vars) in
           SVS.elements svs
       in

       TransSys.mk_trans_sys [] (* scope *) state_vars
         init trans [] props TransSys.Horn
         
     | _ -> assert false)
    
  | Some s -> match s with 

    (* (set-info ...) *)
    | HStringSExpr.List (HStringSExpr.Atom s :: _) when s == s_set_info -> 

      (* Skip *)
      parse acc sym_p_opt lexbuf

    (* (set-logic HORN) *)
    | HStringSExpr.List [HStringSExpr.Atom s; HStringSExpr.Atom l]
      when s == s_set_logic && l == s_horn -> 

      (* Skip *)
      parse acc sym_p_opt lexbuf

    (* (set-logic ...) *)
    | HStringSExpr.List [HStringSExpr.Atom s; e] when s == s_set_logic -> 

      raise 
        (Failure 
           (Format.asprintf 
              "@[<hv>Invalid logic %a, must be HORN" 
              HStringSExpr.pp_print_sexpr e))

    (* (declare-fun p a r) *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; 
         HStringSExpr.Atom p; 
         HStringSExpr.List a; 
         (HStringSExpr.Atom _ as r)]
      when s == s_declare_fun && p == s_pred -> 

      (* Types of argument of monolithic predicate *)
      let arg_types = List.map Conv.type_of_string_sexpr a in

      (* Types of result of monolithic predicate *)
      let res_type = Conv.type_of_string_sexpr r in

      (* Declare predicate *)
      let sym_p = 
        Symbol.mk_symbol 
          (`UF 
             (UfSymbol.mk_uf_symbol
                (HString.string_of_hstring p) 
                arg_types
                res_type))
      in

      let _, vars_0, vars_1 =
        List.fold_left 
          (fun (i, vars_0, vars_1) t -> 

             let sv = 
               StateVar.mk_state_var
                 (Format.sprintf "Y%d" i)
                 [] (* scope? *)
                 t
             in

             (succ i, 
              (Var.mk_state_var_instance sv Numeral.zero) :: vars_0, 
              (Var.mk_state_var_instance sv Numeral.one) :: vars_1))
          (1, [], [])
          arg_types
      in

      (* Continue *)
      parse acc (Some (sym_p, List.rev vars_0, List.rev vars_1)) lexbuf

    (* (declare-fun ...) *)
    | HStringSExpr.List (HStringSExpr.Atom s :: e :: _) 
      when s == s_declare_fun -> 

      raise 
        (Failure 
           (Format.asprintf 
              "@[<hv>Invalid predicate declaration %a, only the monolithic \
               predicate %a allowed@]" 
              HStringSExpr.pp_print_sexpr e
              HString.pp_print_hstring s_pred))

    (* (assert ...) *)
    | HStringSExpr.List [HStringSExpr.Atom s; e] when s == s_assert -> 

      (match sym_p_opt with 

       | None -> 

         raise 
           (Failure 
              (Format.asprintf 
                 "Predicate %a must be declared before assert"
                 HString.pp_print_hstring s_pred))

       | Some (sym_p, vars_0, vars_1) -> 

         (* Format.eprintf "SEXPR: %a@." HStringSExpr.pp_print_sexpr e; *)

         let expr = Conv.expr_of_string_sexpr e in

         (* Format.eprintf "EXPR: %a@." Term.pp_print_term expr; *)
         let clause = clause_of_expr expr in
         (* List.iter (Format.eprintf " - CJ CLAUSE: %a@." Term.pp_print_term) clause; *)
         
         let var_pos, var_neg, clause' = classify_clause sym_p clause in

         let acc = add_horn acc [] (* scope? *)
             clause' vars_0 vars_1 var_pos var_neg in

         (* Continue *)
         parse acc sym_p_opt lexbuf)


    (* (check-sat) *)
    | HStringSExpr.List [HStringSExpr.Atom s] when s == s_check_sat -> 

      (* Skip *)
      parse acc sym_p_opt lexbuf

    | e -> 

      raise 
        (Failure 
           (Format.asprintf 
              "@[<hv>Unexpected S-expression@ @[<hv 1>%a@]@]" 
              HStringSExpr.pp_print_sexpr e))


(* Parse SMTLIB2 Horn format from channel *)
let of_channel in_ch =   

  (* Initialise buffer for lexing *)
  let lexbuf = Lexing.from_channel in_ch in

  parse ([], [], []) None lexbuf


(* Parse SMTLIB2 Horn format from file *)
let of_file filename = 

  (* Open the given file for reading *)
  let use_file = open_in filename in
  let in_ch = use_file in

  let transSys = of_channel in_ch in

  debug horn
     "%a"
     TransSys.pp_print_trans_sys transSys
  in

  (* Format.eprintf "------- TRANSITION SYSTEM ---------\n\n %a@." *)
  (*   TransSys.pp_print_trans_sys transSys; *)

  transSys

      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
