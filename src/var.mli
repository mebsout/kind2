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

(** Variables in terms

    A variable is an instance of a state variable (see {!StateVar}) in
    a state relative to an initial state. A variable can also be a
    free variable that is to be bound in a let expression.

    @author Christoph Sticksel *)

(** {1 Types and hash-consing} *)

(** Hashconsed variable *)
type t


(** {1 Hashtables, maps and sets} *)

(** Comparison function on variables *)
val compare_vars : t -> t -> int

(** Equality function on variables *)
val equal_vars : t -> t -> bool

(** Hashing function on variables *)
val hash_var : t -> int

(** Hash table over variables *)
module VarHashtbl : Hashtbl.S with type key = t

(** Set over variables *)
module VarSet : Set.S with type elt = t

(** Map over variables *)
module VarMap : Map.S with type key = t


(** {1 Constructor} *)

(** Return a constant state variable 

    The state variable must be constant. *)
val mk_const_state_var : StateVar.t -> t

(** Return an instance of a state variable 

    The state variable may also be constant, in which case a variable
    created by [mk_const_state_var] is returned. *)
val mk_state_var_instance : StateVar.t -> Numeral.t -> t

(** Return a free variable *)
val mk_free_var : HString.t -> Type.t -> t

(** Return a fresh free variable *)
val mk_fresh_var : Type.t -> t

(** Import a variable from a different instance into this hashcons table *)
val import : t -> t

(** {1 Accessor functions} *)

(** Return the type of the variable *)
val type_of_var : t -> Type.t

(** Return the state variable of a state variable instance *)
val state_var_of_state_var_instance : t -> StateVar.t

(** Return the offset of a state variable instance *)
val offset_of_state_var_instance : t -> Numeral.t

(** Return a string for a free variable *)
val hstring_of_free_var : t -> HString.t

(** Return true if the variable is an instance of a state variable *)
val is_state_var_instance : t -> bool

(** Return true if the variable is a constant state variable *)
val is_const_state_var : t -> bool

(** Return true if the variable is a free variable *)
val is_free_var : t -> bool

(** Add to the offset of a state variable instance

    Negative values are allowed *)
val bump_offset_of_state_var_instance : Numeral.t -> t -> t   

(** Return a state variable instance at the given offset *)
val set_offset_of_state_var_instance : Numeral.t -> t -> t   

(** {1 Pretty-printing} *)

(** Pretty-print a hashconsed variable *)
val pp_print_var : Format.formatter -> t -> unit

(** Pretty-print a hashconsed variable to the standard formatter *)
val print_var : t -> unit

(** Return a string representation of a hashconsed variable *)
val string_of_var : t -> string 

val stats : unit -> int * int * int * int * int * int

(** Gets the state var instance associated with a constant unrolled
    uf. Throws [Not_found] if the uf is unknown. *)
val state_var_instance_of_symbol : Symbol.t -> t

(** Gets the state var instance associated with a constant unrolled
    uf. Throws [Not_found] if the uf is unknown. *)
val state_var_instance_of_uf_symbol : UfSymbol.t -> t

val unrolled_uf_of_state_var_instance : t -> UfSymbol.t

(** Declares constant variables as constant ufsymbols using the
    provided function. *)
val declare_constant_vars : (UfSymbol.t -> unit) -> t list -> unit

(** Declares non constant variables as constant ufsymbols using the
    provided function. *)
val declare_vars : (UfSymbol.t -> unit) -> t list -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
