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

(** Conversion of a counterexample to a Lustre model 

    @author Kevin Clancy, Christoph Sticksel *)

(** Output a counterexample as a Lustre execution in XML format *)
val pp_print_path_xml : LustreNode.t list -> bool -> Format.formatter -> Model.path -> unit

(** Output a counterexample as a Lustre execution as plain text with
    pre-processing reverted *)
val pp_print_path_pt : LustreNode.t list -> bool -> Format.formatter -> Model.path -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
