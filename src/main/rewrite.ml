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
    Debug.print_program p';
    Debug.print_message comment;
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
  let p = do_step "Scoping done" Debug.print_program Scoping.program p in
  (* Write defined variables for equations *)
  let p = do_step "Write done" Debug.print_program Write.program p in

  (* Source to source transformations start here *)
  let p = transform_and_compare "Static reduction" Static.program genv0 p in
    
  (* Inlining *)
  let _ = transform_and_compare "Inlining" Inline.program genv0 p in

  ()
