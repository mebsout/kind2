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

(** Kind's symbols 

    The term representation is modeled after the SMTLIB 2.0 standard
    and the symbols are a subset of the symbols defined in the SMTLIB
    theories {{: http://smtlib.cs.uiowa.edu/theories/Core.smt2}
    Core} and {{: http://smtlib.cs.uiowa.edu/theories/Reals_Ints.smt2}
    Reals_Ints} with the addition of uninterpreted symbols.

    Most symbols are variadic and associativity is to be understood as
    defined in the SMTLIB standard: 
    {ul
    {- [`TRUE] nullary: Boolean true value}
    {- [`FALSE] nullary: Boolean false value}
    {- [`NOT] unary: Boolean negation}
    {- [`IMPLIES] variadic, right-associative: Boolean implication}
    {- [`AND] variadic, left-associative: Boolean conjunction}
    {- [`OR] variadic, left-associative: Boolean disjunction}
    {- [`XOR] variadic, left-associative: Boolean exclusice disjunction}
    {- [`EQ] variadic, chainable: equality between terms }
    {- [`DISTINCT] variadic, pairwise: distict predicate on terms }
    {- [`ITE] ternary: if-then-else}
    {- [`NUMERAL i] nullary: integer numeral}
    {- [`DECIMAL f] nullary: floating-point decimal}
    {- [`BV b] nullary: onstant bitvector}
    {- [`MINUS] variadic, left-associative: difference or a unary negation}
    {- [`PLUS] variadic, left-associative: sum}
    {- [`TIMES] variadic, left-associative: product}
    {- [`DIV] variadic, left-associative: real quotient }
    {- [`INTDIV] variadic, left-associative: integer quotient }
    {- [`MOD] binary: modulus}
    {- [`ABS] unary: absolute value}
    {- [`LEQ] chainable: less than or equal relation}
    {- [`LT] chainable: less than relation}
    {- [`GEQ] chainable: greater than or equal relation}
    {- [`GT] chainable: greater than relation}
    {- [`TO_REAL] unary: conversion to a real number }
    {- [`TO_INT] unary: conversion to an integer number }
    {- [`IS_INT] unary: real is an integer}
    {- [`DIVISIBLE n] unary: divisibilibty by n}
    {- [`CONCAT] binary: concatenation of bitvectors }
    {- [`EXTRACT (i, j)] unary: extract subsequence from bitvector}
    {- [`BVNOT] unary: bit-wise negation}
    {- [`BVNEG] unary: arithmetic negation (unary)}
    {- [`BVAND] binary: bit-wise conjunction}
    {- [`BVOR] binary: bit-wise disjunction}
    {- [`BVADD] binary: arithmetic sum}
    {- [`BVMUL] binary: arithmetic multiplication}
    {- [`BVDIV] binary: arithmetic integer division}
    {- [`BVUREM] binary: arithmetic remainder}
    {- [`BVSHL] unary: logical shift left}
    {- [`BVLSHR] unary: logical shift right}
    {- [`BVULT] binary: arithmetic comparision}
    {- [`SELECT] binary: selection from array}
    {- [`STORE] ternary: update of an array}
    }

    A chainable symbol is to be read as the conjunction of successive
    pairs, for example [(<= 1 2 3)] is equivalent to [(and (<= 1 2)
    (<= 2 3))]. A pairwise symbol is to be read as the conjunction of
    each pair of arguments, for example [(distinct a b c)] is [(and
    (distinct a b) (distinct a c) (distinct b c))].

    In addition to these interpreted symbols we use the following symbols 
    {ul
    {- [`UF u] variadic: uninterpreted symbol}
    }

    Symbols are hashconsed so that we can rely on physical equality
    for comparison, however, as of now there are no useful properties
    to be stored alongside symbols. In particular the [`NUMERAL i],
    [`DECIMAL f] and [`SYM (s, t)] symbols need to be hashconsed for
    physical equality.

    @author Christoph Sticksel *)


(** {1 Types and hash-consing} *)

(** The interpreted symbols *)
type interpreted_symbol = 
  [ `TRUE                 (** Boolean true value (nullary) *)
  | `FALSE                (** Boolean false value (nullary) *)
  | `NOT                  (** Boolean negation (unary) *)
  | `IMPLIES              (** Boolean implication (right-associative) *)
  | `AND                  (** Boolean conjunction (left-associative) *)
  | `OR                   (** Boolean disjunction (left-associative) *)
  | `XOR                  (** Boolean exclusive disjunction (left-associative)*)

  | `EQ                   (** Equality between terms (chainable) *)
  | `DISTINCT             (** Pairwise distinct predicate (chainable) *)
  | `ITE                  (** If-then-else (ternary)*) 

  | `NUMERAL of Numeral.t (** Infinite precision integer numeral (nullary) *)
  | `DECIMAL of Decimal.t  (** infinite precision floating-point decimal (nullary) *)
(*
  | `BV of Lib.bitvector    (** Constant bitvector *)
*)
  | `MINUS                (** Difference or unary negation (left-associative) *)
  | `PLUS                 (** Sum (left-associative) *)
  | `TIMES                (** Product (left-associative) *)
  | `DIV                  (** Real quotient (left-associative) *)
  | `INTDIV               (** Integer quotient (left-associative) *)
  | `MOD                  (** Modulus (binary) *)
  | `ABS                  (** Absolute value (unary) *)
  | `LEQ                  (** Less than or equal relation (chainable) *)
  | `LT                   (** Less than relation (chainable) *)
  | `GEQ                  (** Greater than or equal relation (chainable) *)
  | `GT                   (** Greater than relation (chainable) *)
  | `TO_REAL              (** Conversion to a floating-point decimal (unary) *)
  | `TO_INT               (** Conversion to an integer numeral (unary) *)
  | `IS_INT               (** Real is an integer (unary) *)

  | `DIVISIBLE of Numeral.t
                          (** Divisible by [n] (unary) *)
(*
  | `CONCAT               (** Concatenation of bitvectors (binary) *)
  | `EXTRACT of Numeral.t * Numeral.t 
                          (** Extract subsequence from bitvector (unary) *)
  | `BVNOT                (** Bit-wise negation (unary) *)
  | `BVNEG                (** Arithmetic negation (unary) *)
  | `BVAND                (** Bit-wise conjunction (binary) *)
  | `BVOR                 (** Bit-wise disjunction (binary) *)
  | `BVADD                (** Arithmetic sum (binary) *)
  | `BVMUL                (** Arithmetic multiplication (binary) *)
  | `BVDIV                (** Arithmetic integer division (binary) *)
  | `BVUREM               (** Arithmetic remainder (binary) *)
  | `BVSHL                (** Logical shift left (unary) *)
  | `BVLSHR               (** Logical shift right (unary) *)
  | `BVULT                (** Arithmetic comparision (binary) *)
*)

  | `SELECT               (** Selection from array (binary) *)
(*
  | `STORE                (** Update of an array (ternary) *)
*)
  ]

(** Adding uninterpreted function symbols separately for conversions
    from expressions in the SMT solver interface *)
type symbol =
  [ interpreted_symbol
  | `UF of UfSymbol.t     (** Uninterpreted symbol (fixed arity) *)
  ]

(** Hashconsed symbol *)
type t


(** {1 Hashtables, maps and sets} *)

(** Comparison function on symbols *)
val compare_symbols : t -> t -> int

(** Equality function on symbols *)
val equal_symbols : t -> t -> bool

(** Hashing function on symbols *)
val hash_symbol : t -> int

(** Hash table over symbols *)
module SymbolHashtbl : Hashtbl.S with type key = t

(** Set over symbols *)
module SymbolSet : Set.S with type elt = t

(** Map over symbols *)
module SymbolMap : Map.S with type key = t

(** {1 Constructor} *)

(** Create a symbol *)
val mk_symbol : symbol -> t

(** Import symbol from a different instance into this hashcons table *)
val import : t -> t

(** {1 Static symbols} *)

(** Constant Boolean value symbol *)
val s_true : t

(** Constant Boolean value symbol *)
val s_false : t

(** Constant negation symbol *)
val s_not : t

(** Constant conjunction symbol *)
val s_and : t

(** Constant disjunction symbol *)
val s_or : t

(** Constant implication symbol *)
val s_implies : t

(** Constant equality symbol *)
val s_eq : t

(** Constant greater than or equal symbol *)
val s_geq : t

(** Constant less than or equal symbol *)
val s_leq : t

(** Constant greater than symbol *)
val s_gt : t

(** Constant less than symbol *)
val s_lt : t

(** Constant modulus operator symbol *)
val s_mod : t

(** Constant minus operator symbol *)
val s_minus : t

(** Constant plus operator symbol *)
val s_plus : t

(** Constant times operator symbol *)
val s_times : t

(** Constant division operator symbol *)
val s_div : t

(** Array read operator *)
val s_select : t



(** {1 Accessors functions} *)

(** Return the node of the hashconsed symbol *)
val node_of_symbol : t -> symbol

(** Return true if the symbol is a numeral *)
val is_numeral : t -> bool

(** Return true if the symbol is a decimal *)
val is_decimal : t -> bool
(*
(** Return true if the symbol is a bitvector *)
val is_bitvector : t -> bool
*)
(** Return true if the symbol is [`TRUE] or [`FALSE] *)
val is_bool : t -> bool

(** Return the numeral in a [`NUMERAL _] symbol *)
val numeral_of_symbol : t -> Numeral.t 

(** Return the decimal in a [`DECIMAL _] symbol *)
val decimal_of_symbol : t -> Decimal.t 
(*
(** Return the bitvector in a [`BV _] symbol *)
val bitvector_of_symbol : t -> Lib.bitvector 
*)
(** Return [true] for the [`TRUE] symbol and [false] for the [`FALSE]
    symbol *)
val bool_of_symbol : t -> bool 

(** Return true if the symbol is uninterpreted *)
val is_uf : t -> bool

(** Return the uninterpreted symbol of a symbol *)
val uf_of_symbol : t -> UfSymbol.t

(** {1 Pretty-printing} *)

(** Pretty-print a symbol *)
val pp_print_symbol : Format.formatter -> t -> unit

(** Return a string representation of a symbol *)
val string_of_symbol : t -> string 

(** Return a string representation of a symbol *)
val string_of_symbol_node : symbol -> string 

val stats : unit -> int * int * int * int * int * int

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
