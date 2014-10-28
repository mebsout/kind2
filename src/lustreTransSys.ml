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


(* Abbreviations *)
module I = LustreIdent
module E = LustreExpr
module N = LustreNode

module VS = Var.VarSet
module SVS = StateVar.StateVarSet


(* Name of uninterpreted function symbol for initial state constraint *)
let init_uf_symbol_name_of_node n = 
  Format.asprintf
    "%s_%a"
    I.init_uf_string
    (LustreIdent.pp_print_ident false) n
 

(* Name of uninterpreted function symbol for transition relation  *)
let trans_uf_symbol_name_of_node n = 
  Format.asprintf
    "%s_%a"
    I.trans_uf_string
    (LustreIdent.pp_print_ident false) n


(* TODO: use Set.S.of_list of OCaml 4.02 for better performance *)

(* Set of state variables of list *)
let svs_of_list list = 
  List.fold_left (fun a e -> SVS.add e a) SVS.empty list


(* Add a list of state variables to a set *)
let add_to_svs set list = 
  List.fold_left (fun a e -> SVS.add e a) set list 


(* Create a copy of the state variable at the top level *)
let state_var_of_top_scope is_input ?is_const ?is_clock top_node state_var =

  let top_scope_index = I.index_of_ident top_node in

  let state_var' = 
    E.mk_state_var_of_ident 
      is_input
      (StateVar.is_const state_var)
      top_scope_index
      (fst (E.ident_of_state_var state_var))
      (StateVar.type_of_state_var state_var)
  in

  (* State variable is instance of local variable *)
  E.set_state_var_source
    state_var'
    E.Abstract;

  (* Variable is an instance of a variable *)
  E.set_state_var_instance state_var' LustreAst.dummy_pos top_node state_var;

  state_var'
  


(* Collect information while constructing transition system *)
type node_def =

  { 

    (* Transition system for node *)
    trans_sys : TransSys.t;

    (* Input variables *)
    inputs : StateVar.t list;

    (* Output variables *)
    outputs : StateVar.t list;

    (* Stateful local variables *)
    locals : StateVar.t list;

    (* Properties in node *)
    props : (string * Term.t) list;

    (* Assumptions in contract of node *)
    requires : Term.t list;

    (* Guarantees in contract of node *)
    ensures : Term.t list;

  }



(* Fold list of equations to definitions 

   [definitions_of_equations s i t e] takes as input the list of free
   (stateful and signature) state variables [s], two list of terms [i]
   and [t] to be taken as a conjunction of, respectively, the initial
   state constraint and the transition relation, and a list [e] of

   If a state variable is in the list of free variables, add an
   equation for its value in the initial state and in the transition
   to [i] and [t], respectively. Otherwise form the conjunction of [i]
   and [t] separately and add a let binding of the variable to its
   definition to each. 

   Assume that definitions of variables that are not free do not contain
   variables that are only defined later in the list. *)
let rec definitions_of_equations vars init trans = function 

  (* All equations consumed, return terms for initial state constraint
     and transition relation *)
  | [] -> (init, trans)

  (* Take first equation and term for init and step *)
  | (state_var, ({ E.expr_init; E.expr_step } as expr)) :: tl -> 

    (* Modified definitions *)
    let init', trans' = 

      if 

        (* Variable must to have a definition? *)
        SVS.mem state_var vars

      then 

        (

          (* Equation for initial constraint on variable *)
          let init_def = 
            Term.mk_eq 
              [E.base_term_of_state_var TransSys.init_base state_var; 
               E.base_term_of_expr TransSys.init_base expr_init] 
          in

          (* Equation for transition relation on variable *)
          let trans_def = 
            Term.mk_eq 
              [E.cur_term_of_state_var TransSys.trans_base state_var; 
               E.cur_term_of_expr TransSys.trans_base expr_step] 
          in

          (* Add terms of equation *)
          (init_def :: init, trans_def :: trans))

      else

        (

          (* Define variable with a let *)
          let init' =
            Term.mk_let 
              [(E.base_var_of_state_var TransSys.init_base state_var, 
                E.base_term_of_expr TransSys.init_base expr_init)] 
              (Term.mk_and init) 
          in

          (* Define variable with a let *)
          let trans' = 
            Term.mk_let
              [(E.cur_var_of_state_var TransSys.trans_base state_var, 
                E.cur_term_of_expr TransSys.trans_base expr_step)] 
              (Term.mk_and trans)
          in

          (* Start with singleton lists of let-bound terms *)
          ([init'], [trans']))

    in
    
    (* Continue with next equations *)
    definitions_of_equations vars init' trans' tl


(* Fold list of node calls and return terms

   Local variables of the called node are instantiated to fresh local
   variables of the calling node and returned. 

   Properties of the called node are instantiated to properties of the
   calling node and returned.

   Assumptions in the contract of the called node are instantiated to
   properties of the calling node and returned.

   A node call always has an activation condition, which may be the
   constant true. In this case the default values for the outputs are
   ignored and the list may be the empty list.

   The initial state of the calling node is constrained by the
   predicate of the initial state constraint of the called, and
   analogously for the transition relation.

   The parameters of the initial state predicate are (in this order) 
   - the inputs, 
   - the variables capturing the outputs, 
   - the observer variables for the properties of the called node, and 
   - the instances of the local variables of the called node.

   The parameters of the transition relation are (in this order) 
   - the inputs at the next step, including constant inputs 
   - the variables capturing the outputs at the next step,
   - the observer variables for the properties of the called node at
     the next step, 
   - the instances of the local variables of the called node at the
     next step,
   - the inputs at the previous step, excluding constant inputs,
   - the variables capturing the outputs at the previous step,
   - the observer variables for the properties of the called node at
     the previous step, and
   - the instances of the local variables of the called node at the
     previous step.

   If a node call has an activation condition that is not the constant
   true, additional fresh variables are generated. One variable is
   initially false and becomes and remains true on the first time the
   activation condition is true. Further, all input variables are
   duplicated to shadow input variables that freeze the input values
   at the last instant the activation condition has been true.

   The initial state constraint of the called node is a conjunction of
   formulas representing the following:
   - the ticked flag is true if and only if to the activation
     condition is true in the initial instant,
   - the shadow input variables take the values of the actual input
     variables if the activation condition is true, and
   - the initial state predicate of the called node with the
     parameters as above, except for the input variables that are
     replaced by the shadow input variables.

   The transition relation of the called node is a conjunction of
   formulas representing the following facts:

   - the ticked flag is true in the next state if it has been true in
     the previous instant, or if if to the activation condition is
     true,

   - the shadow input variables in the next state take the values of
     the actual input variables if the activation condition is true,
     and their previous values if the activation condition is false.

   - the initial state predicate of the called node with the
     parameters as above, except for the input variables that are
     replaced by the shadow input variables, if the activation
     condition is true in the next step and the ticked flag is false
     in the previous step, and

   - the transition relation predicate of the called node with the
     parameters as above, except for the input variables that are
     replaced by the shadow input variables, if the activation
     condition is true and the ticked flag is true in the previous
     step.

*)
let rec definitions_of_node_calls 
    mk_ticked_state_var
    mk_new_state_var
    node_defs
    local_vars
    init
    trans
    lifted_props = 

  function

    (* All node calls consumed, return term for initial state
       constraint and transition relation, and properties  *)
    | [] -> (local_vars, init, trans, lifted_props)

    (* Node call with or without activation condition *)
    | { N.call_returns = output_vars;
        N.call_observers = observer_vars;
        N.call_clock = act_cond;
        N.call_node_name = node_name;
        N.call_inputs = input_vars;
        N.call_defaults = init_exprs;
        N.call_pos = pos } as call :: tl -> 
(*
      debug lustreTransSys
          "definitions_of_node_calls: %a"
          (N.pp_print_call false) call
      in
*)
      let 

        (* Get additional information about called node *)
        { trans_sys;
          inputs; 
          outputs; 
          locals;
          props;
          requires;
          ensures } = 

        (* Find called node by name *)
        try 
          
          List.assoc node_name node_defs 
            
        with Not_found -> assert false

      in

      (* Predicate for initial state constraint *)
      let init_uf_symbol = TransSys.init_uf_symbol trans_sys in

      (* Predicate for initial state constraint *)
      let trans_uf_symbol = TransSys.trans_uf_symbol trans_sys in

      (* Initial state value of activation condition *)
      let act_cond_init = 
        E.base_term_of_expr TransSys.init_base act_cond.E.expr_init 
      in 

      (* Step state value of activation condition *)
      let act_cond_step = 
        E.cur_term_of_expr TransSys.trans_base act_cond.E.expr_step 
      in 

      (* Previous step state value of activation condition *)
      let act_cond_step_pre = 
        E.pre_term_of_expr TransSys.trans_base act_cond.E.expr_step 
      in

      (* Initial state values of default values *)
      let init_terms_init = 
        List.map 
          (function { E.expr_init } -> 
            E.base_term_of_expr TransSys.init_base expr_init) 
          init_exprs
      in

      (* Input for node call in initial state *)
      let input_terms_init = 
        List.map
          (E.base_term_of_state_var TransSys.init_base)
          input_vars
      in

      (* Input for node call in step state *)
      let input_terms_step = 
        List.map
          (E.cur_term_of_state_var TransSys.trans_base)
          input_vars
      in

      (* Input for node call in step state

         Skip over constant state variables *)
      let input_terms_step_pre = 
        List.fold_right2
          (fun sv sv' accum -> 
             if StateVar.is_const sv then 
               accum 
             else
               E.pre_term_of_state_var TransSys.trans_base sv' :: accum)  
          inputs
          input_vars
          []
      in

      (* Variables capturing the output of the node in the initial
         state *)
      let output_terms_init = 
        List.map (E.base_term_of_state_var TransSys.init_base) output_vars
      in

      (* Variables capturing the output of the node in the current
         state *)
      let output_terms_step = 
        List.map (E.cur_term_of_state_var TransSys.trans_base) output_vars
      in

      (* Variables capturing the output of the node in the previous
         state *)
      let output_terms_step_pre = 
        List.map (E.pre_term_of_state_var TransSys.trans_base) output_vars
      in

      (* Variables observing properties in called nodes in the initial
         state *)
      let observer_terms_init = 
        List.map (E.base_term_of_state_var TransSys.init_base) observer_vars
      in

      (* Variables observing properties in called nodes in the current
         state *)
      let observer_terms_step = 
        List.map (E.cur_term_of_state_var TransSys.trans_base) observer_vars
      in

      (* Variables observing properties in called nodes in the
         previous state *)
      let observer_terms_step_pre = 
        List.map (E.pre_term_of_state_var TransSys.trans_base) observer_vars
      in

      (* Stateful variables local to the node for this instance *)
      let local_vars', call_local_vars = 

        (* Need to preserve order of variables *)
        List.fold_right
          (fun state_var (local_vars, call_local_vars) -> 

             (* Type of state variable *)
             let var_type = StateVar.type_of_state_var state_var in

             (* Name of state variable *)
             let var_name = StateVar.string_of_state_var state_var in

             (* New state variable for node call *)
             let local_state_var = mk_new_state_var var_type in

             (* State variable is not defined in input *)
             E.set_state_var_source local_state_var E.Abstract;

             (* State variable is an instance of a local variable *)
             E.set_state_var_instance
               local_state_var
               pos
               node_name state_var;

             (local_state_var :: local_vars, 
              local_state_var :: call_local_vars))
          locals

          (* Observers are not locals, but become outputs *)
          (input_vars @ output_vars @ local_vars, [])

      in

      (* Variables local to node call for current state *)
      let call_local_vars_init = 
        List.map (E.base_term_of_state_var TransSys.init_base) call_local_vars
      in

      (* Variables local to node call for previous state *)
      let call_local_vars_step = 
        List.map (E.cur_term_of_state_var TransSys.trans_base) call_local_vars
      in

      (* Variables local to node call for previous state *)
      let call_local_vars_step_pre = 
        List.map (E.pre_term_of_state_var TransSys.trans_base) call_local_vars
      in

      (* Arguments for node call in initial state *)
      let init_call_args = 

        (* Current state input variables *)
        input_terms_init @ 

        (* Current state output variables *)
        output_terms_init @ 

        (* Current state output variables *)
        observer_terms_init @ 

        (* Current state local variables *)
        call_local_vars_init

      in

      (* Arguments for node call in transition relation *)
      let step_call_args = 

        (* Current state input variables *)
        input_terms_step @ 

        (* Current state output variables *)
        output_terms_step @ 

        (* Current state output variables *)
        observer_terms_step @ 

        (* Current state local variables *)
        call_local_vars_step @

        (* Previous state input variables *)
        input_terms_step_pre @

        (* Previous state output variables *)
        output_terms_step_pre @

        (* Previous state output variables *)
        observer_terms_step_pre @

        (* Previous state local variables *)
        call_local_vars_step_pre  

      in

      (* Constraint for node call in initial state *)
      let init_call = 
        Term.mk_uf init_uf_symbol init_call_args 
      in

      (* Constraint for node call in transition relation *)
      let trans_call = 
        Term.mk_uf trans_uf_symbol step_call_args 
      in

      (* Lift properties from called node *)
      let lifted_props' = 

        (* Pretty-print a file position *)
        let pp_print_file ppf pos_file = 

          if pos_file = "" then () else
            Format.fprintf ppf "%s" pos_file

        in

        (* Pretty-print a position as attributes *)
        let pp_print_pos ppf pos = 

          (* Do not print anything for a dummy position *)
          if LustreAst.is_dummy_pos pos then () else 

            (* Get file, line and column of position *)
            let pos_file, pos_lnum, pos_cnum = 
              LustreAst.file_row_col_of_pos pos
            in

            (* Print attributes *)
            Format.fprintf 
              ppf
              "[%al%dc%d]"
              pp_print_file pos_file
              pos_lnum
              pos_cnum

        in

        (* Lift the name of a property in a subnode by adding the
           position of the node call *)
        let lift_prop_name node_name pos prop_name =

          string_of_t 
            (function ppf -> function prop_name -> 
               Format.fprintf ppf 
                 "%a%a.%s"
                 (LustreIdent.pp_print_ident true) node_name
                 pp_print_pos pos
                 prop_name)
            prop_name

        in

        (* Lift properties in subnode to properties of calling node *)
        List.map 
          (function (n, t) -> 
            (lift_prop_name node_name pos n, 
             LustreExpr.lift_term pos node_name t))
          props 

      in

      (* TODO: lift assumptions of contract of called node as
         properties *)

      (* Constraint for node call in initial state and transition
         relation with activation condition *)
      let 

        local_vars'', 
        init_call_act_cond, 
        trans_call_act_cond, 
        lifted_props'' = 

        if 

          (* Activation condition of node is constant true *)
          E.equal_expr act_cond E.t_true

        then 

          (* Return predicates unguarded *)
          local_vars', init_call, trans_call, lifted_props @ lifted_props'

        else

          (* Create fresh state variable for node call *)
          let ticked_state_var = mk_ticked_state_var () in

          (* State variable to mark if clock has ever ticked in the
             initial state *)
          let ticked_init =
            E.base_term_of_state_var TransSys.init_base ticked_state_var 
          in

          (* State variable to mark if clock has ever ticked in the
             current state *)
          let ticked_step =
            E.cur_term_of_state_var TransSys.trans_base ticked_state_var 
          in

          (* State variable to mark if clock has ever ticked in the
             previous state *)
          let ticked_step_pre =
            E.pre_term_of_state_var TransSys.trans_base ticked_state_var 
          in

          (* Create shadow variable for each non-constant input *)
          let 
            
            (* Add shadow state variable to local variables, return
               term at previous instant, equation with corresponding
               inputs, and equation with previous state value *)
            (local_vars'', 
             input_shadow_terms_step_pre, 
             propagate_inputs, 
             propagate_inputs_init, 
             interpolate_inputs) =

            List.fold_right
              (fun
                sv
                ((local_vars'',
                  input_shadow_terms_step_pre, 
                  propagate_inputs, 
                  propagate_inputs_init, 
                  interpolate_inputs) as accum) -> 

                (* Skip over constant inputs *)
                if StateVar.is_const sv then accum else 

                  (* Create fresh shadow variable for input *)
                  let sv' = mk_new_state_var (StateVar.type_of_state_var sv) in

                  (* State variable is locally created *)
                  E.set_state_var_source sv' E.Abstract;

                  (* Shadow variable at previous instant *)
                  let t = E.pre_term_of_state_var TransSys.trans_base sv' in

                  (* Shadow variable takes value of input *)
                  let p = 
                    Term.mk_eq
                      [E.cur_term_of_state_var TransSys.trans_base sv'; 
                       E.cur_term_of_state_var TransSys.trans_base sv]
                  in

                  (* Shadow variable takes value of input *)
                  let p_i = 
                    Term.mk_eq
                      [E.base_term_of_state_var TransSys.init_base sv'; 
                       E.base_term_of_state_var TransSys.init_base sv]
                  in

                  (* Shadow variable takes its previous value *)
                  let i = 
                    Term.mk_eq
                      [E.cur_term_of_state_var TransSys.trans_base sv'; 
                       E.pre_term_of_state_var TransSys.trans_base sv']
                  in

                  (* Add shadow variable and equations to accumulator *)
                  (sv' :: local_vars'',
                   t :: input_shadow_terms_step_pre, 
                   p :: propagate_inputs, 
                   p_i :: propagate_inputs_init, 
                   i :: interpolate_inputs))
              input_vars
              (local_vars', [], [], [], [])

          in

          (* Arguments for node call in initial state constraint
             with state variables at next step *)
          let init_call_step_args = 

            (* Current state input variables *)
            input_terms_step @ 

            (* Current state output variables *)
            output_terms_step @ 

            (* Current state output variables *)
            observer_terms_step @ 

            (* Current state local variables *)
            call_local_vars_step 

          in

          (* Constraint for node call in initial state *)
          let init_call_trans = 
            Term.mk_uf init_uf_symbol init_call_step_args 
          in

          (* Arguments for node call in transition relation *)
          let trans_call_args = 

            (* Current state input variables *)
            input_terms_step @ 

            (* Current state output variables *)
            output_terms_step @ 

            (* Current state output variables *)
            observer_terms_step @ 

            (* Current state local variables *)
            call_local_vars_step @

            (* Previous state input variables *)
            input_shadow_terms_step_pre @

            (* Previous state output variables *)
            output_terms_step_pre @

            (* Previous state output variables *)
            observer_terms_step_pre @

            (* Previous state local variables *)
            call_local_vars_step_pre  

          in

          (* Constraint for node call in transition relation *)
          let trans_call = Term.mk_uf trans_uf_symbol trans_call_args in

          (* Local variables extended by state variable indicating if
             node has ticked once *)
          (ticked_state_var :: local_vars'',

           Term.mk_and

             (* Initial state constraint *)
             [

               (* Equation for ticked state variable *)
               Term.mk_eq [ticked_init; act_cond_init];

               (* Propagate input values to shadow variable on clock tick *)
               Term.mk_implies 
                 [act_cond_init; Term.mk_and propagate_inputs_init];

               (* Initial state constraint with true activation
                  condition *)
               Term.mk_implies [act_cond_init; init_call];

               (* Initial state constraint with false activation
                  condition *)
               Term.mk_implies 
                 [Term.mk_not act_cond_init;
                  Term.mk_and
                    (List.fold_left2 
                       (fun accum state_var { E.expr_init } ->
                          Term.mk_eq 
                            [E.base_term_of_state_var
                               TransSys.init_base
                               state_var; 
                             E.base_term_of_expr
                               TransSys.init_base
                               expr_init] :: 
                          accum)
                       []
                       (output_vars @ observer_vars)
                       (init_exprs @ 
                        (List.map (fun _ -> E.t_true) observer_vars)))]

             ],

           (* Transition relation *)
           Term.mk_and

             [

               (* State variable is false if the clock has not ticked before *)
               Term.mk_eq 
                 [ticked_step;
                  Term.mk_or [act_cond_step; ticked_step_pre]];

               (* Propagate input values to shadow variable on clock tick *)
               Term.mk_implies 
                 [act_cond_step; Term.mk_and propagate_inputs];

               (* Interpolate input values in shadow variable between
                  clock ticks *)
               Term.mk_implies 
                 [Term.mk_not act_cond_step; Term.mk_and interpolate_inputs];

               (* Transition relation with true activation condition
                  on the first clock tick *)
               Term.mk_implies
                 [Term.mk_and 
                    [act_cond_step; Term.mk_not ticked_step_pre];
                  init_call_trans];

               (* Transition relation with true activation condition
                  on following clock ticks *)
               Term.mk_implies
                 [Term.mk_and 
                    [act_cond_step; ticked_step_pre];
                  trans_call];

               (* Transition relation with false activation condition *)
               Term.mk_implies 
                 [Term.mk_not act_cond_step;
                  Term.mk_and 
                    (List.fold_left
                       (fun accum state_var ->
                          Term.mk_eq 
                            [E.cur_term_of_state_var
                               TransSys.trans_base 
                               state_var; 
                             E.pre_term_of_state_var
                               TransSys.trans_base
                               state_var] :: 
                          accum)
                       []
                       (output_vars @ observer_vars @ call_local_vars))];

             ],

           lifted_props @ lifted_props')

      in

      (* Continue with next node call *)
      definitions_of_node_calls 
        mk_ticked_state_var
        mk_new_state_var
        node_defs
        local_vars''
        (init_call_act_cond :: init)
        (trans_call_act_cond :: trans) 
        lifted_props''
        tl


(* Fold list of expressions to lists of initial state and transition
   relation terms *)
let rec definitions_of_exprs init trans = 

  function

    (* All assertions consumed, return term for initial state
       constraint and transition relation *)
    | [] -> (init, trans)

    (* Assertion with term for initial state and term for transitions *)
    | { E.expr_init; E.expr_step } as expr :: tl ->

      (* Term for assertion in initial state *)
      let term_init = E.base_term_of_expr TransSys.init_base expr_init in 

      (* Term for assertion in step state *)
      let term_step = E.cur_term_of_expr TransSys.trans_base expr_step in 

      (* Add constraint unless it is true *)
      let init' = 
        if Term.equal term_init Term.t_true then init else term_init :: init 
      in

      (* Add constraint unless it is true *)
      let trans' = 
        if Term.equal term_step Term.t_true then trans else term_step :: trans 
      in

      (* Continue with next assertions *)
      definitions_of_exprs init' trans' tl
      

(* Fold list of assertions and return terms *)
let definitions_of_asserts = definitions_of_exprs


(* Return assumptions and guarantees from contract *)
let definitions_of_contract requires ensures = 

  let init_requires, step_requires = 
    definitions_of_exprs [] [] requires 
  in

  let init_ensures, step_ensures = 
    definitions_of_exprs [] [] ensures 
  in

  (init_requires, init_ensures), (step_requires, step_ensures)


(* Return a property term from a property *)
let prop_of_node_prop main_node state_var =

  (* Name of state variable is name of property *)
  let prop_name = StateVar.name_of_state_var state_var in
  
  (* Term of property *)
  let prop_term = 
    E.base_term_of_state_var 
      TransSys.init_base
      (state_var_of_top_scope false main_node state_var) 
  in
  
  (prop_name, prop_term)


(* Return node definitions of nodes *)
let rec trans_sys_of_nodes' nodes node_defs = function 

  (* All nodes converted, now create the top-level formulas *)
  | [] -> 

    (match node_defs with 

      (* List of nodes must not be empty *)
      | [] -> raise (Invalid_argument "trans_sys_of_nodes")

      (* Return transition system of top node *)
      | (_, { trans_sys }) :: _ -> trans_sys

    )

(*

      (* Take the head of the list as top node *)
      | (_, { inputs; outputs; locals; props}) :: _, 
        (init_uf_symbol, (init_vars, _)) :: _,
        (trans_uf_symbol, (trans_vars, _)) :: _ -> 

        (* Create copies of the state variables of the top node,
           flagging input variables *)
        let state_vars_top = 
          List.map
            (state_var_of_top_scope true main_node) 
            inputs @
          List.map
            (state_var_of_top_scope false main_node) 
            (outputs @ locals)
        in

        let state_vars_top_pre = 
          List.map 
            (state_var_of_top_scope true main_node)
            (List.filter (fun sv -> not (StateVar.is_const sv)) inputs) @
          List.map
            (state_var_of_top_scope false main_node)
            (outputs @ locals)
        in

        let init_terms =
         List.map (E.base_term_of_state_var TransSys.init_base) state_vars_top
        in

        let trans_terms =
          ((List.map (E.cur_term_of_state_var TransSys.trans_base) state_vars_top) @
           (List.map (E.pre_term_of_state_var TransSys.trans_base) state_vars_top_pre))
        in

        (

          (* Definitions of predicates for initial state constraint *)
          List.rev fun_defs_init, 

          (* Definitions of predicates for transition relation *)
          List.rev fun_defs_trans, 

          (* State variables *)
          state_vars_top, 

          (init_uf_symbol, (List.combine init_vars init_terms)),

          (trans_uf_symbol, (List.combine trans_vars trans_terms)),

(*
          (* Initial state constraint *)
          Term.mk_uf 
            init_uf_symbol
            (List.map (E.base_term_of_state_var TransSys.init_base) state_vars_top),

          (* Transition relation *)
          Term.mk_uf 
            trans_uf_symbol
            ((List.map (E.cur_term_of_state_var TransSys.trans_base) state_vars_top) @
             (List.map (E.pre_term_of_state_var TransSys.trans_base) state_vars_top_pre)),
*)

          List.map
            (function (n, t) -> 
              (n, LustreExpr.lift_term LustreAst.dummy_pos main_node t)) 
            props

        )

      (* List of nodes must not be empty *)
      | _ -> raise (Invalid_argument "trans_sys_of_nodes")

    )
*)


  | ({ N.name = node_name;
       N.inputs = node_inputs;
       N.oracles = node_oracles;
       N.outputs = node_outputs; 
       N.observers = node_observers;
       N.locals = node_locals; 
       N.equations = node_equations; 
       N.calls = node_calls; 
       N.asserts = node_asserts; 
       N.props = node_props; 
       N.requires = node_requires; 
       N.ensures = node_ensures } as node) :: tl ->

    debug lustreTransSys
        "@[<v>trans_sys_of_node:@,@[<hv 1>%a@]@]"
        (N.pp_print_node false) node
    in

    (* Return true if the state variable is an input or output *)
    let is_input_or_output sv = 

      (List.exists 
         (fun (sv', _) -> (StateVar.equal_state_vars sv sv'))
         node_inputs)
      || (List.exists 
            (fun (sv', _) -> (StateVar.equal_state_vars sv sv'))
            node_outputs)
      || (List.exists
            (StateVar.equal_state_vars sv) 
            node_oracles)
      || (List.exists
            (StateVar.equal_state_vars sv) 
            node_observers)

    in

    (* Create scope from node name *)
    let scope = LustreIdent.index_of_ident node_name in

    (* Previous value of index of ticked flag for condact

       Keep in this function to reset index for each node *)
    let ticked_state_var_index = ref Numeral.(- one) in

    (* Create a fresh state variable to flag first tick of node *)
    let mk_ticked_state_var () = 

      (* Create fresh state variable *)
      let state_var =
        E.mk_fresh_state_var
          false
          false
          (LustreIdent.index_of_ident node_name)
          I.ticked_ident
          Type.t_bool
          ticked_state_var_index
      in

      (* State variable is abstract *)
      E.set_state_var_source
        state_var
        E.Abstract;

      (* Return state variable *)
      state_var

    in

    (* Create a fresh state variable for abstractions *)
    let mk_new_state_var state_var_type = 
      E.mk_fresh_state_var
        false
        false
        scope
        I.abs_ident
        state_var_type
        node.N.fresh_state_var_index
    in

    (* Input variables *)
    let inputs = List.map fst node_inputs in

    (* Oracle input variables *)
    let oracles = node_oracles in

    (* Output variables *)
    let outputs = List.map fst node_outputs in

    (* Observer output variables *)
    let observers = node_observers in

    (* Add constraints from node calls *)
    let call_locals, init_defs_calls, trans_defs_calls, lifted_props = 
      definitions_of_node_calls 
        mk_ticked_state_var
        mk_new_state_var
        node_defs
        []
        []
        []
        []
        node_calls
    in

    (* Variables capturing outputs of node calls are new local
       variables unless they are inputs or outputs *)
    let call_locals_set = 
      svs_of_list
        (List.filter (fun sv -> not (is_input_or_output sv)) call_locals)
    in

    debug lustreTransSys
        "@[<hv>Call local vars in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        (SVS.elements call_locals_set)
    in

    (* Variables occurring under a pre are new local variables unless
       they are inputs or outputs *)
    let node_locals_set = 
      SVS.filter 
        (fun sv -> not (is_input_or_output sv))
        (N.stateful_vars_of_node node)
    in

    debug lustreTransSys
        "@[<hv>Node local vars in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        (SVS.elements node_locals_set)
    in

    (* Local variables are those occurring under a pre, properties or
       variables capturing outputs of node calls *)
    let locals_set = 
      List.fold_left 
        SVS.union
        SVS.empty
        [node_locals_set; call_locals_set]
    in

    (* Convert set to a list *)
    let locals = SVS.elements locals_set in

    debug lustreTransSys
        "@[<hv>Local vars in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        locals
    in


    (* Variables visible in the signature of the definition are local
       variables, inputs and outputs *)
    let signature_vars_set = 
      List.fold_left 
        add_to_svs 
        locals_set
        [inputs; outputs; oracles; observers]
    in

    debug lustreTransSys
        "@[<hv>Stateful vars in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        (SVS.elements signature_vars_set)
    in


    (* Constraints from assertions

       Must add assertions and contract first so that local variables
       can be let bound in definitions_of_equations *)
    let (init_defs_asserts, trans_defs_asserts) = 
      definitions_of_asserts  
        init_defs_calls
        trans_defs_calls
        node_asserts
    in

    (* Constraints from equations *)
    let (init_defs_eqs, trans_defs_eqs) = 
      definitions_of_equations 
        signature_vars_set
        init_defs_asserts
        trans_defs_asserts
        (List.rev node_equations)
    in

    (* Types of variables in the signature *)
    let signature_types = 
      (List.map StateVar.type_of_state_var inputs) @ 
      (List.map StateVar.type_of_state_var oracles) @ 
      (List.map StateVar.type_of_state_var outputs) @ 
      (List.map StateVar.type_of_state_var observers) @ 
      (List.map StateVar.type_of_state_var locals) 
    in

    debug lustreTransSys
        "@[<hv>Inputs in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        inputs
    in

    debug lustreTransSys
        "@[<hv>Oracles in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        oracles
    in

    debug lustreTransSys
        "@[<hv>Outputs in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        outputs
    in

    debug lustreTransSys
        "@[<hv>Observers in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        observers
    in

    debug lustreTransSys
        "@[<hv>Locals in %a:@ @[<hv>%a@]@]"
        (I.pp_print_ident false) node_name
        (pp_print_list StateVar.pp_print_state_var ",@ ")
        locals
    in

    (* Symbol for initial state constraint for node *)
    let init_uf_symbol = 
      UfSymbol.mk_uf_symbol

        (* Name of symbol *)
        (init_uf_symbol_name_of_node node_name)

        (* Types of variables in the signature *)
        signature_types 

        (* Symbol is a predicate *)
        Type.t_bool

    in

    (* Symbol for initial state constraint for node *)
    let pred_def_init = 

      (* Name of symbol *)
      (init_uf_symbol,

       (* Input variables *)
       (((List.map (E.base_var_of_state_var TransSys.init_base) inputs) @

         (* Oracle inputs *)
         (List.map (E.base_var_of_state_var TransSys.init_base) oracles) @

         (* Output variables *)
         (List.map 
            (E.base_var_of_state_var TransSys.init_base) 
            outputs) @

         (* Observer variables *)
         (List.map 
            (E.base_var_of_state_var TransSys.init_base) 
            observers) @

         (* Local variables *)
         (List.map (E.base_var_of_state_var TransSys.init_base) locals)),

        (Term.mk_and init_defs_eqs)))

    in

    (* Symbol for transition relation for node *)
    let trans_uf_symbol = 
      UfSymbol.mk_uf_symbol

        (* Name of symbol *)
        (trans_uf_symbol_name_of_node node_name)

        (* Types of variables in the signature *)
        (signature_types @ signature_types)

        (* Symbol is a predicate *)
        Type.t_bool

    in

    (* Symbol for initial state constraint for node *)
    let pred_def_trans = 

      (trans_uf_symbol,

       (* Input variables *)
       (((List.map (E.cur_var_of_state_var TransSys.trans_base) inputs) @

         (* Oracle inputs *)
         (List.map (E.cur_var_of_state_var TransSys.trans_base) oracles) @

         (* Output variables *)
         (List.map 
            (E.cur_var_of_state_var TransSys.trans_base)
            outputs) @

         (* Observer output variables *)
         (List.map 
            (E.cur_var_of_state_var TransSys.trans_base)
            observers) @

         (* Local variables *)
         (List.map (E.cur_var_of_state_var TransSys.trans_base) locals) @ 

         (* Input variables *)
         (List.fold_right 
            (fun sv accum -> 
               if StateVar.is_const sv then
                 accum
               else
                 E.pre_var_of_state_var TransSys.trans_base sv :: accum)
            inputs
            []) @

         (* Output variables *)
         (List.map (E.pre_var_of_state_var TransSys.trans_base) outputs) @

         (* Observer output variables *)
         (List.map (E.pre_var_of_state_var TransSys.trans_base) observers) @

         (* Local variables *)
         (List.map (E.pre_var_of_state_var TransSys.trans_base) locals)),

        (Term.mk_and trans_defs_eqs)))

    in

    debug lustreTransSys
        "@[<v>Transition relation:@,%a@]"
        TransSys.pp_print_uf_def pred_def_trans
    in

    let props = 
      (List.map 
         (function state_var -> 

           (* Name of state variable is name of property *)
           let prop_name = StateVar.name_of_state_var state_var in

           (* Term of property *)
           let prop_term = 
             E.base_term_of_state_var 
               TransSys.init_base
               state_var
           in
           (prop_name, prop_term))
         node_props)
      @ lifted_props
    in

    debug lustreTransSys
        "@[<hv>Properties of node %a@ @[<hv>%a@]@]"
        (LustreIdent.pp_print_ident false) node_name
        (pp_print_list
           (function ppf -> function (n, t) -> 
              Format.fprintf ppf 
                "%s: %a"
                n
                Term.pp_print_term t)
           ",@ ")
        props
    in
    
    (* Get list of transition systems of called nodes *)
    let called_trans_sys, called_nodes = 
      
      List.fold_left 

        (* Add transition system of node to accumulator *)
        (fun (t, s) n -> 

           (* Get information about called node *)
           let d = List.assoc n node_defs in
           
           (* Get source of called node *)
           let s' =
             match TransSys.get_source d.trans_sys with 
               | TransSys.Lustre nodes -> 
                 List.fold_left
                   (fun a n -> 
                      if List.mem n a then a else n :: a)
                   s
                   nodes 
               | _ -> assert false
           in

           (d.trans_sys :: t, s'))

        ([], [])
        
        (* List of identifiers of called nodes without duplicates *)
        (I.LustreIdentSet.elements
           (List.fold_left 
              (fun a e -> I.LustreIdentSet.add e.N.call_node_name a)
              I.LustreIdentSet.empty
              node_calls))

    in

    (* Create transition system for node *)
    let trans_sys = 
      TransSys.mk_trans_sys 
        (I.scope_of_ident node_name)
        (inputs @ oracles @ outputs @ observers @ locals)
        pred_def_init
        pred_def_trans
        called_trans_sys
        props
        (TransSys.Lustre (List.rev (node :: called_nodes)))
    in

    debug lustreTransSys
      "%a"
      TransSys.pp_print_trans_sys trans_sys
    in

    (* Create record for this node *)
    let node_def = 
      { trans_sys = trans_sys;
        inputs = inputs @ oracles;
        outputs = outputs @ observers;
        locals = locals;
        props = props;
        requires = [];
        ensures = [] }
    in

    (* Continue with next nodes *)
    trans_sys_of_nodes'
      (node :: nodes)
      ((node_name, node_def) :: node_defs)
      tl


let trans_sys_of_nodes nodes = trans_sys_of_nodes' [] [] nodes


let props_of_nodes main_node nodes = 

  try 

    let { LustreNode.props } = LustreNode.node_of_name main_node nodes in

    List.map 
      (prop_of_node_prop main_node)
      props


  with Not_found -> 
    raise 
      (Failure 
         (Format.asprintf
            "props_of_nodes: Node %a not found" 
            (LustreIdent.pp_print_ident false) main_node))


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
