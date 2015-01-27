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

(** Parser for verification problems in the Horn clauses format  

    @author Christoph Sticksel
    @author Alain Mebsout
 *)



(** Parse from the file Parse SMTLIB2 Horn format from file and construct an
    internal transition system. The input problem must be in a (big) monolithic
    predicate used in exactly 3 Horn Clauses.

    This is to be used with the following converter (for the moment):
    http://www.philipp.ruemmer.org/mono-lazabs.jar

    To convert from SMT-LIB2 Horn format to a monolithic system in SMT-LIB2,
    call the program with arguments

    java -jar mono-lazabs.jar -horn -hsmt -bup -logSimplified \
    /tmp/gopan.c.nts.smt2

    (the example is from
    https://svn.sosy-lab.org/software/sv-benchmarks/trunk/clauses/LIA/Eldarica/MONNIAUX/gopan.c.nts.smt2)

    Similarly, for Prolog inputs:

    java -jar mono-lazabs.jar -horn -hin -bup -logSimplified <filename>

    In any case, the resulting SMT-LIB2 problem is still in Horn format, but
    contains exactly three clauses (written using SMT-LIB Boolean operators,
    and explicit quantifiers for all variables). The single and only predicate
    must be named {p}:

    I(s) => p(s)
    p(s) & T(s, s') => p(s')
    p(s) & !Prop(s) => false

*)
val of_file : string -> TransSys.t 


(** Pretty-print a counter example *)
val pp_print_path_pt :
  Format.formatter -> (StateVar.t * Term.t list) list -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
