(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zélus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* static inlining; warning: this step must be done after static reduction *)
(* function calls [inline f e1 ... en] are inlined *)

open Misc
open Ast
open Value
open Error
open Mapfold

let error { kind; loc } =
  Format.eprintf "Error during inlining\n";
  Error.message loc kind;
  raise Error

(* returns [let p1' = e1 and ... and pn' = en in e[p1'/p1,...,p'n/pn] *)
(* in which [p1,...,pn] are renamed into [p1',...,pn'] and [e] is *)
(* recursively inlined *)
        (*
          let letin renaming env p_list e_list e =
  let eqmake p e = eqmake (EQeq(p, e)) in

  let env, renaming0 = build env in
  let renaming = Env.append renaming0 renaming in
  let p_list = List.map (pattern renaming) p_list in
  { e with e_desc =
      Elet({ l_rec = false; l_env = env; l_eq = List.map2 eqmake p_list e_list;
             l_loc = Zlocation.no_location }, expression renaming e) }
         *)

let expression funs acc ({ e_desc } as e) =
  match e_desc with
  | Eapp { is_inline = true;
           f = { e_desc = Eglobal { lname }; e_loc = f_loc }; arg_list } ->
     (* a function call [inline f e1 ... en] is replaced by *)
     (* [let x1 = e1 in ... let xn = en in
         local o do eq in o_res] *)
     (* if [f = [fun|node] p1...pn returns o eq] *)
     let { Genv.info } = Genv.find lname acc in
     begin match info with
     | Vclosure
       { c_funexp = { f_vkind; f_kind; f_atomic; f_args; f_body;
                               f_env }; c_genv; c_env } ->
        (* letin renaming env p_list e_list *)
        e, acc
     | _ -> error { kind = Etype; loc = f_loc }
     end
  | _ -> raise Mapfold.Fallback
