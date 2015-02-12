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
open SolverResponse


exception Unknown

(* Generate next unique identifier *)
let gentag =
  let r = ref 0 in
  fun () -> incr r; !r


(* Instantiate module for SMTLIB2 solvers with drivers *)
module Z3SMTLIB : SolverSig.S = SMTLIBSolver.Make (Z3Driver)
module CVC4SMTLIB : SolverSig.S = SMTLIBSolver.Make (CVC4Driver)
module MathSat5SMTLIB : SolverSig.S = SMTLIBSolver.Make (MathSAT5Driver)
module Yices2SMTLIB : SolverSig.S = SMTLIBSolver.Make (Yices2SMT2Driver)

(* SMT expression *)
type expr = SMTExpr.t


(* Solver instance *)
type t =

  { 
    
    (* Type of SMT solver *)
    solver_kind : Flags.smtsolver;
    
    (* Solver instance *)
    solver_inst : (module SolverSig.Inst);
    
    (* Hashtable associating generated names to terms *)
    term_names : (int, expr) Hashtbl.t;

    (* Unique identifier for solver instance *)
    id : int

  }

(* Raise an exception on error responses from the SMT solver *)
let fail_on_smt_error = function       

  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))

  | `Unsupported -> 
    raise 
      (Failure 
         ("SMT solver reported not implemented"))

  | `NoResponse ->
    raise 
      (Failure 
         ("SMT solver did not produce a reply"))

  | _ -> () 


(* ******************************************************************** *)
(* Creating and finalizing a solver instance                            *)
(* ******************************************************************** *)

let bool_of_bool_option = function
  | None -> false
  | Some b -> b

(* Create a new instance of an SMT solver, declare all currently created
   uninterpreted function symbols *)
let create_instance
    ?produce_assignments
    ?produce_proofs
    ?produce_cores
    l
    kind =

  (* New identifier for solver instance *)
  let id = gentag () in

  (* Module for parameters of solver instance *)
  let module Params = 
  struct
    let produce_assignments = bool_of_bool_option produce_assignments
    let produce_proofs = bool_of_bool_option produce_proofs
    let produce_cores = bool_of_bool_option produce_cores
    let logic = l
    let id = id
  end
  in

  (* Module for solver from options *)
  let fomodule =
    match kind with
    | `Z3_SMTLIB -> (module Z3SMTLIB.Create(Params) : SolverSig.Inst)
    | `CVC4_SMTLIB -> (module CVC4SMTLIB.Create(Params) : SolverSig.Inst)
    | `MathSat5_SMTLIB -> (module MathSat5SMTLIB.Create(Params) : SolverSig.Inst)
    | `Yices_SMTLIB ->  (module Yices2SMTLIB.Create(Params) : SolverSig.Inst)
    | `Yices_native -> (module YicesNative.Create(Params) : SolverSig.Inst)
    | `detect -> assert false
  in

  (* Return solver instance *)
  { solver_kind = kind;
    solver_inst = fomodule;
    term_names = Hashtbl.create 19;
    id = id }


(* Delete a solver instance *)
let delete_instance s =
  let module S = (val s.solver_inst) in
  S.delete_instance ()


(* ******************************************************************** *)
(* Declarations                                                         *)
(* ******************************************************************** *)

(* Declare an uninterpreted function symbol *) 
let declare_fun s uf_symbol =
  let module S = (val s.solver_inst) in

  fail_on_smt_error 
    (S.declare_fun
       (UfSymbol.string_of_uf_symbol uf_symbol)
       (UfSymbol.arg_type_of_uf_symbol uf_symbol)
       (UfSymbol.res_type_of_uf_symbol uf_symbol))


(* Define an uninterpreted function symbol *)
let define_fun s uf_symbol vars term =
  let module S = (val s.solver_inst) in

  fail_on_smt_error 
    (S.define_fun
       (UfSymbol.string_of_uf_symbol uf_symbol)
       vars
       (UfSymbol.res_type_of_uf_symbol uf_symbol)
       term)



(* ******************************************************************** *)
(* Primitives                                                           *)
(* ******************************************************************** *)

(* Assert an SMT expression *)
let assert_expr s expr =
  let module S = (val s.solver_inst) in
  (* Assert SMT expression in solver instance and fail on error *)
  fail_on_smt_error (S.assert_expr expr)


(* Convert a term to an SMT expression and assert *)
let assert_term s term =
  let module S = (val s.solver_inst) in

  (* Convert term to SMT expression *)
  let expr = S.Conv.smtexpr_of_term term in

  (* Assert SMT expression in solver instance and fail on error *)
  fail_on_smt_error (S.assert_expr expr)


(* Name a term with a fresh name, convert to an SMT expression and
   assert, returning the name *)
let assert_named_term s term = 

  let term_name, term' = Term.mk_named term in

  Hashtbl.add s.term_names term_name term;

  assert_term s term'


(* Push a new scope to the context and fail on error *)
let push ?(n = 1) s =
  let module S = (val s.solver_inst) in
  fail_on_smt_error (S.push n) 

(* Pop a new scope from the context and fail on error *)
let pop ?(n = 1) s =
  let module S = (val s.solver_inst) in
  fail_on_smt_error (S.pop n)


(* ******************************************************************** *)
(* Satisfiability checks                                                *)
(* ******************************************************************** *)

let prof_check_sat ?(timeout = 0) s =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_check_sat_time;
  let res = S.check_sat ~timeout () in
  Stat.record_time Stat.smt_check_sat_time;
  res

let prof_check_sat_assuming s exprs =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_check_sat_time;
  let res = S.check_sat_assuming exprs in
  Stat.record_time Stat.smt_check_sat_time;
  res

let prof_get_value s e =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_get_value_time;
  let res = S.get_value e in
  Stat.record_time Stat.smt_get_value_time;
  res

let prof_get_model s e =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_get_value_time;
  let res = S.get_model e in
  Stat.record_time Stat.smt_get_value_time;
  res


(* Check satisfiability of current context *)
let check_sat ?(timeout = 0) s = 

  (* Check satisfiability *)
  match prof_check_sat ~timeout s with 

  (* Return true if satisfiable *)
  | `Sat -> true

  (* Return false if unsatisfiable *)
  | `Unsat -> false

  (* Fail on unknown *)
  | `Unknown -> raise Unknown

  (* Fail on error *)
  | `Error _ as r -> 
    fail_on_smt_error r; 
    failwith "SMT solver returned Success on check-sat"


(* Convert models given as pairs of SMT expressions to pairs of
   variables and terms *)
let values_of_smt_values conv_left type_left s smt_values =
  let module S = (val s.solver_inst) in

  (* Convert association list for get-value call to an association
     list of variables to terms *)
  List.map

    (* Map pair of SMT expressions to a pair of variable and term *)
    (function (v, e) -> 

      (* Convert to variable or term and term *)
      let v', e' = 
        conv_left v, S.Conv.term_of_smtexpr e 
      in

      (* Get type of variable or term and term *)
      let tv', te' = 
        type_left v', Term.type_of_term e'
      in

      if 
        (* Assignment of integer value to a real variable or term? *)
        Type.equal_types tv' Type.t_real && 
        Type.equal_types te' Type.t_int 

      then

        (* Convert integer to real *)
        (v', Term.mk_to_real e')

      else

        (* Keep assignment *)
        (v', e'))

    smt_values


let model_of_smt_values conv_left type_left s smt_values = 
  let module S = (val s.solver_inst) in

  (* Create hash table with size matching the number of values *)
  let model = Var.VarHashtbl.create (List.length smt_values) in

  (* Add all variable term pairs to the hash table *)
  List.iter

    (* Convert a pair of SMT expressions to a variable and a term, and
       add to the hash table *)
    (function (v, e) ->

      (* Convert expression on lhs to a variable and expression on rhs
         to a term *)
      let v', e' = 
        let t = S.Conv.var_term_of_smtexpr v in
        (* TODO: deal with arrays *)
        assert (Term.is_free_var t);
        Term.free_var_of_term t, S.Conv.term_of_smtexpr e 
      in

      (* Get types of variable and term *)
      let tv', te' = 
        Var.type_of_var v', Term.type_of_term e'
      in

      (* Hack to make integer values match reals *)
      let e'' =

        if 

          (* Rhs is of type real, variable is of type integer? *)
          Type.is_real tv' && 
          (Type.is_int te' || Type.is_int_range te')
          
        then

          (* Convert term to a real *)
          Term.mk_to_real e'

        else
          
          (* Return term as is *)
          e'

      in        

      (* Add assignment to hash table *)
      Var.VarHashtbl.add model v' (Model.Term e''))

    (* Iterate over all pairs from get-value call *)
    smt_values;

  (* Return hash table *)
  model

let model_of_smt_model s smt_model vars = 
  let module S = (val s.solver_inst) in

  (* Create hash table with size matching the number of values *)
  let model = Var.VarHashtbl.create (List.length smt_model) in

  (* Add all variable term pairs to the hash table *)
  List.iter
    (fun v -> 

       let uf_sym = Var.unrolled_uf_of_state_var_instance v in

       try

         let t_or_l = List.assq uf_sym smt_model in

         Var.VarHashtbl.add model v t_or_l 

       with Not_found -> ()

(*
         Event.log L_debug "No assignment to %a" Var.pp_print_var v;

         assert false
*)
    )
    vars;

  model
  

let partial_model_of_smt_model s smt_model = 
  let module S = (val s.solver_inst) in

  (* Create hash table with size matching the number of values *)
  let model = Var.VarHashtbl.create (List.length smt_model) in

  (* Add all variable term pairs to the hash table *)
  List.iter
    (fun (uf_sym, t_or_l) -> 

       try 

         let var = Var.state_var_instance_of_uf_symbol uf_sym in
         
         Var.VarHashtbl.add model var t_or_l

       with Not_found -> ())
    smt_model;

  model
  

(* Get values of terms in the current context *)
let get_term_values s terms =
  let module S = (val s.solver_inst) in

  match 
    (* Get values of SMT expressions in current context *)
    prof_get_value s (List.map S.Conv.smtexpr_of_term terms) 
  with 
  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))

  | `Values m -> 
    values_of_smt_values S.Conv.term_of_smtexpr Term.type_of_term s m

(* Raise when encountering an array variable to switch to get-model
   instead of get-value *)
exception Var_is_array

(* Get model of the current context *)
let get_var_values s vars =
  let module S = (val s.solver_inst) in

  match 

    (* Get values of SMT expressions in current context *)
    prof_get_value s

      (* Map variables to terms and raise exception if a variable is
         of array type *)
      (List.map
         (fun v -> 
            if Var.type_of_var v |> Type.is_array then
              raise Var_is_array
            else
              S.Conv.smtexpr_of_var v [])
         vars)

  with 

    | `Error e -> 
      raise 
        (Failure ("SMT solver failed: " ^ e))

    | `Values v -> 

      model_of_smt_values 

        (* Convert an SMT term back to a variable *)
        (fun v -> 
           let t = S.Conv.var_term_of_smtexpr v in

           (* We are sure that there are no array typed variables *)
           assert (Term.is_free_var t); 
           (Term.free_var_of_term t))

        Var.type_of_var 
        s 
        v

    | exception Var_is_array -> 

      (
        match 

          (* Get model in current context *)
          prof_get_model s ()

        with 

          | `Error e -> 
            raise 
              (Failure ("SMT solver failed: " ^ e))
              
          | `Model m ->

            model_of_smt_model s m vars

      )


(* Get model of the current context *)
let get_model s =
  let module S = (val s.solver_inst) in

  match 
    
    (* Get model in current context *)
    prof_get_model s ()

  with 
    
    | `Error e -> 
      raise 
        (Failure ("SMT solver failed: " ^ e))
        
    | `Model m ->
      
      partial_model_of_smt_model s m 


(* Get unsat core of the current context *)
let get_unsat_core_of_names s =
  let module S = (val s.solver_inst) in

  match S.get_unsat_core () with 

  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))

  | `Unsat_core c -> 

    try 

      (* Convert strings t<int> to integer *)
      let core_names = 
        List.map 
          (function s -> Scanf.sscanf s "t%d" (function x -> x)) 
          c
      in

      List.fold_left 
        (fun a n -> Hashtbl.find s.term_names n :: a)
        []
        core_names

    with

    (* Raise exception if scanning fails *)
    | Scanf.Scan_failure _
    | End_of_file
    | Failure _ -> 
      raise (Failure "Invalid string in reply from SMT solver")

        
(* Get unsat core of the current context *)
let get_unsat_core_lits s =
  let module S = (val s.solver_inst) in

  match S.get_unsat_core () with 

  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))

  | `Unsat_core c -> 

    (* Convert strings to literals *)
    List.fold_left  
      (fun a s -> 
        try 
          (Term.mk_uf 
             (UfSymbol.uf_symbol_of_string s)
             []) :: a
        with Not_found -> assert false)
      []
      c

      
(* ******************************************************************** *)
(* Higher level functions                                               *)
(* ******************************************************************** *)

(* Checks satisfiability of some literals, runs if_sat if sat and if_unsat if
   unsat. *)
let check_sat_assuming s if_sat if_unsat literals =

  let module S = (val s.solver_inst) in
  
  if S.check_sat_assuming_supported () then

    (* Solver supports check-sat-assuming, let's do this. *)
    let sat =

      match

        (* Performing the check-sat. *)
        S.check_sat_assuming literals

      with

        (* Fail on error *)
        | `Error e -> 
          raise 
            (Failure ("SMT solver failed: " ^ e))
            
        (* Return true if satisfiable *)
        | `Sat -> true
          
        (* Return false if unsatisfiable *)
        | `Unsat -> false
          
        (* Fail on unknown *)
        | `Unknown -> raise Unknown
                        
    in
    
    (* Executing user-provided functions. *)
    if sat then if_sat () else if_unsat () 
      
  else
    
    (* Solver does not support check-sat-assuming, doing
       push/pop. *)

    (* Pushing. *)
    let _ = push s in
    
    (* Asserting literals. *)
    literals |> Term.mk_and |> assert_term s ;
    
    (* Performing check-sat. *)
    let sat = check_sat s in
    
    (* Executing user-defined functions. *)
    let res = if sat then if_sat () else if_unsat () in

    pop s;
    
    res
    
let execute_custom_command s cmd args num_res =
  let module S = (val s.solver_inst) in
  S.execute_custom_command cmd args num_res

let execute_custom_check_sat_command cmd s =
  let module S = (val s.solver_inst) in
  S.execute_custom_check_sat_command cmd



(* ******************************************************************** *)
(* Utiliy functions                                                     *)
(* ******************************************************************** *)

let converter s =
  let module S = (val s.solver_inst) in
  (module S.Conv : SMTExpr.Conv)


let kind s = s.solver_kind


let trace_comment s c =
  let module S = (val s.solver_inst) in
  S.trace_comment c


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
