(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the main functions *)
open Misc
open Location
open Monad
open Result
open Value
open Lident
open Find
open Primitives
open Error
open Coiteration
               
exception Stop

let lexical_error err loc =
  Format.eprintf "%aIllegal character.@." output_location loc;
  raise Error

let syntax_error loc =
  Format.eprintf "%aSyntax error.@." output_location loc;
  raise Error

let parse parsing_fun lexing_fun source_name =
  let ic = open_in source_name in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.Lexing.lex_curr_p <-
    { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = source_name };
  try
    parsing_fun lexing_fun lexbuf
  with
  | Lexer.Lexical_error(err, loc) ->
     close_in ic; lexical_error err loc
  | Parser.Error ->
     close_in ic;
     syntax_error
       (Loc(Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf))
     
let parse_implementation_file source_name =
  parse Parser.implementation_file Lexer.main source_name
               
           
let apply_with_close_out f o =
  try
    f o;
    close_out o
  with x -> close_out o; raise x

let do_step comment output step input = 
  let o = step input in
  Debug.print_message comment;
  output o;
  o

let compare n_steps genv0 p p' =
  let genv = Coiteration.program genv0 p in
  let genv' = Coiteration.program genv0 p' in
  Coiteration.check n_steps genv genv'; p'
    
(* Apply a sequence of source-to-source transformation *)
(* do equivalence checking for every step if the flag is turned on *)
let main ff modname filename source_name otc n_steps =
  let transform_and_compare comment transform genv p =
    let p' = transform genv p in
    Debug.print_message comment;
    Debug.print_program p';
    if n_steps = 0 then p' else compare n_steps genv p p' in
    
  (* set the current opened module *)
  Location.initialize source_name;

  (* Parsing *)
  let p = parse_implementation_file source_name in
  Debug.print_message "Parsing done";

  (* defines the initial global environment for values *)
  let genv0 = Genv.initialize modname [] in
  (* Add Stdlib *)
  let genv0 = Genv.add_module genv0 Primitives.stdlib_env in
  
  (* Associate unique index to variables *)
  let p = do_step "Scoping done. See below:" Debug.print_program
            Scoping.program p in
  (* Write defined variables for equations *)
  let p = do_step "Write done. See below: " Debug.print_program Write.program p in
  (* Source to source transformations start here *)
  let p = transform_and_compare "Static reduction done. See below:"
            Static.program genv0 p in
  (* Inlining *)
  let p = transform_and_compare "Inlining done" Inline.program genv0 p in
  (* Normalise derivative equations - remove the handler () *)
    let p = transform_and_compare
              "Remove handlers in definitions of derivatives. See below:"
              Der.program genv0 p in
  let p = transform_and_compare
            "Translation of automata. See below:" Automata.program genv0 p in
  let p = transform_and_compare
	    "Compilation of memories (fby/pre) into (init/last). See below:"
	     Pre.program genv0 p in
  let _ = transform_and_compare
            "Compilation of initialization and resets. See below:"
            Reset.program genv0 p in
  ()
      (*
      let impl_list =
        step "Remove last in pattern. See below:"
             Remove_last_in_patterns.implementation_list impl_list in
      let impl_list =
        step "Add a copy for [last x] to remore false cycles. See below:"
             Add_copy_for_last.implementation_list impl_list in
      let impl_list =
        step "Translation of automata done. See below:"
             Automata.implementation_list impl_list in
      let impl_list =
        step "Translation of activations done. See below:"
             Activate.implementation_list impl_list in
      let impl_list =
        step "Translation of present done. See below:"
             Present.implementation_list impl_list in
      let impl_list =
        step "Translation of periods done. See below:"
             Period.implementation_list impl_list in
      let impl_list =
        step "Translation of disc done. See below:"
             Disc.implementation_list impl_list in
      let impl_list =
        step "Translation of probabilistic nodes. See below:"
             Proba.implementation_list impl_list in
      let impl_list =
        step
          "Compilation of memories (fby/pre/next) into (init/last). See below:"
             Pre.implementation_list impl_list in
      let impl_list =
        step "Un-nest let/in blocks. See below:"
             Letin.implementation_list impl_list in
      let impl_list =
        step "Compilation of initialization and resets done. See below:"
             Reset.implementation_list impl_list in
      let impl_list =
        step "Actualize write variables in blocks. See below:"
             Write.implementation_list impl_list in
      let impl_list =
        step "Complete equations with [der x = 0.0]. See below:"
            Complete.implementation_list impl_list in
     let impl_list =
        step "Add an extra discrete step for weak transitions. See below:"
            Encore.implementation_list impl_list in
     let impl_list =
        step "Gather all horizons into a single one per function. See below:"
            Horizon.implementation_list impl_list in
     let impl_list =
       step "Translation into A-normal form. See below:"
            Aform.implementation_list impl_list in
     let impl_list =
        step "Actualize write variables in blocks. See below:"
             Write.implementation_list impl_list in
     let impl_list =
       step "Naming shared variables and memories done. See below:"
            Shared.implementation_list impl_list in
     let impl_list =
       step "Common sub-expression elimination. See below:"
            Cse.implementation_list impl_list in
     let impl_list =
       step "Sharing of zero-crossings. See below:"
            Zopt.implementation_list impl_list in
     let impl_list =
       step "Actualize write variables in blocks. See below:"
            Write.implementation_list impl_list in
     let impl_list =
       if not !no_opt && not !no_deadcode
       then step "Deadcode removal. See below:"
                 Zdeadcode.implementation_list impl_list
       else impl_list in
     let impl_list =
       step "Static scheduling done. See below:"
            Schedule.implementation_list impl_list in
     let impl_list =
       if not !no_opt && not !no_deadcode
       then
         let impl_list =
           step "Removing of copy variables done. See below:"
                Copy.implementation_list impl_list in
         step "Deadcode removal. See below:"
              Zdeadcode.implementation_list impl_list
       else impl_list in
     *)
