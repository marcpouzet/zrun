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
               
(* The main entry function. Execute [n] steps of [main()] or [run main ()]  *)
let eval_main genv n_steps main =
  let fv =
    find_gvalue_opt (Name main) genv in
  match fv with
  | None ->
     Format.eprintf "@[Zrun: the global value %s is unbound.@.@]"
       main
  | Some(fv) ->
     match fv with
     | Vclosure({ c_funexp = { f_kind; f_loc; f_args = [[]] } } as c) ->
        begin match f_kind with
        | Knode _ ->
           let si = Coiteration.catch (Coiteration.instance f_loc c) in
           Coiteration.run_node
             no_location (Output.value_flush Format.std_formatter )
             n_steps si void
        | Kfun _ ->
           Coiteration.run_fun
          no_location (Output.value_flush Format.std_formatter )
          n_steps fv [void] end
     | Vclosure({ c_funexp = { f_args = _ } }) ->
        Format.eprintf "@[Zrun: the argument of %s should be void.@.@]" main
     | Vfun _ ->
        Coiteration.run_fun
          no_location (Output.value_flush Format.std_formatter )
          n_steps fv [void]
     | _ ->
        Format.eprintf "@[Zrun: the global value %s is not a function.@.@]"
          main
             
let apply_with_close_out f o =
  try
    f o;
    close_out o
  with x -> close_out o; raise x

let do_step comment step input = 
  let output = step input in
  Debug.print_message comment;
  Debug.print_program output;
  output

let do_optional_stop is_stop p =
  if is_stop then raise Stop else p
  
let do_optional_step is_step comment step p = 
  if is_step then do_step comment step p else p

(* Evaluate all the definition in a file, store values *)
let eval_definitions_in_file modname filename =
  (* output file in which values are stored *)
  let obj_name = filename ^ ".zlo" in
  let otc = open_out_bin obj_name in
    
  let source_name = filename ^ ".zls" in

  (* set the current opened module *)
  Location.initialize source_name;

  (* Parsing *)
  let p = parse_implementation_file source_name in
  Debug.print_message "Parsing done";

  (* defines the initial global environment for values *)
  let genv = Genv.initialize modname [] in
  (* Add Stdlib *)
  let genv = Genv.add_module genv Primitives.stdlib_env in
  
  let p = do_step "Scoping done" Scoping.program p in
  (* Write defined variables for equations *)
  let p = do_step "Write done" Write.program p in
  (* Evaluation of definitions in [filename] *)
  let genv = Coiteration.program genv p in
  Debug.print_message "Evaluation of definitions done";
  
  (* Write the values into a file *)
  apply_with_close_out (Genv.write genv) otc;

  genv

 (* evaluate all nodes/functions whose input is () *)
 let all modname filename n_steps =
   let open Genv in
   let ff = Format.std_formatter in
   let { current = { values } } = eval_definitions_in_file modname filename in
   let eval name v =
     match v with
     (* we make a special treatment for top level functions whose input *)
     (* is () *)
     | Vclosure({ c_funexp = { f_kind; f_loc; f_args = [[]] } } as c) ->
        begin match f_kind with
        | Knode _ ->
           let si = Coiteration.catch (Coiteration.instance f_loc c) in
           Format.fprintf ff "@[Evaluate %d steps of %s@.@]" n_steps name;
           Coiteration.run_node
             no_location (Output.value_flush ff) n_steps si void
        | Kfun _ ->
           Format.fprintf ff "@[Evaluate %d steps of %s@.@]" n_steps name;
           Coiteration.run_fun
             no_location (Output.value_flush ff) n_steps v [void] end
     | _ -> Output.pvalue_flush ff v in
   
     (* evaluate a list of main function/nodes *)
   E.iter eval values
     
 (* evaluate the body of a list of main nodes *)    
 let main modname filename n_steps l_nodes =
   let genv = eval_definitions_in_file modname filename in
     
   (* evaluate a list of main function/nodes *)
   List.iter (eval_main genv n_steps) l_nodes

let transforme_and_compare transform eval compare acc p =
  let p' = transform acc p in
  let v = eval p in
  let v' = eval p' in
  compare v v'

