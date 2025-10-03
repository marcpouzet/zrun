(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2025 Inria Paris                                          *)
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

let total_number_of_iterations_in_fixpoints = ref 0
let compute_total_number_of_iterations_in_fixpoints = ref false
let incr_total_number_of_iterations_in_fixpoints n =
  total_number_of_iterations_in_fixpoints :=
    !total_number_of_iterations_in_fixpoints + n
let reset_total_number_of_iterations_in_fixpoints () = 
  total_number_of_iterations_in_fixpoints := 0
                    
(* remove the check of assertions during evaluation *)
let no_assert = ref false

(* remove the check that fix-point equation produce non bottom values *)
let no_causality = ref false

(* sets the interpretation of the if/then/else to be strict w.r.t the first argument *)
(* this is how the if/then/else is interpreted in Lustre *)
(* if v1 then v2 else v3 = bot if (v1 = bot) or (v2 = bot) or (v3 = bot) *)
let lustre = ref false

(* sets the interpretation of the if/then/else to be such that *)
(* if _ then v1 else v2 = v1 if v1 = v2 *)
(* this is used to implement the constructive causality of Esterel *)
let esterel = ref false

(* static reduction *)
let static_reduction = ref false

let apply_with_close_out f o =
  try
    f o;
    close_out o
  with x -> close_out o; raise x
