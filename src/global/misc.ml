(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2023 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* useful stuff *)

(* error during the whole process *)
exception Error
        
let name_of_stdlib_module = "Stdlib"

let nil_name = "[]"
let cons_name = "::"

let standard_lib = Config.stdlib

(* list of modules initially opened *)
let default_used_modules = ref [name_of_stdlib_module]

(* load paths *)
let load_path = ref ([standard_lib])

let set_stdlib p =
  load_path := [p]

(* where is the standard library *)
let locate_stdlib () =
  Printf.printf "%s\n" standard_lib

let show_version () =
  let open Config in
  Printf.printf "The ZRun Interpreter, version %s-%s (%s)\n"
    version subversion date;
  Printf.printf "Std lib: "; locate_stdlib ();
  Printf.printf "\n";
  ()

let verbose = ref false
let vverbose = ref false
let debug = ref false

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  vverbose := true;
  set_verbose ()

let set_debug () =
  debug := true;
  set_verbose ()

(* the list of nodes to evaluate *)
let main_nodes = ref ([] :string list)
let set_main s = main_nodes := s :: !main_nodes

(* evaluate all nodes *)
let all = ref false
                
let print_values = ref false
                 
(* number of synchronous steps for the evaluation *)
let number_of_steps = ref 0
let set_number_of_steps n = number_of_steps := n

let number_of_fixpoint_iterations = ref 0
let print_number_of_fixpoint_iterations = ref false
let incr_number_of_fixpoint_iterations n =
  number_of_fixpoint_iterations := !number_of_fixpoint_iterations + n
let reset_number_of_fixpoint_iterations () = number_of_fixpoint_iterations := 0
                    
(* remove the check of assertions during evaluation *)
let no_assert = ref false

(* remove the check that fix-point equation produce non bottom values *)
let set_nocausality = ref false

(* sets the interpretation of the if/then/else to Esterel *)
let set_esterel = ref false

(* sets the interpretation of the if/then/else to Lustre *)
let set_lustre = ref false

(* no information associated to expressions *)
type no_info = unit
let no_info: no_info = ()

(* static reduction *)
let set_reduce = ref false
