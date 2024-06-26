(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* rewrite of an [der x = e init e0 reset z1 -> e1 | ... | zn -> en] *)
(* into [present z1 -> x = e1 | ... init x = e0 and der x = e] *)

open Misc
open Location
open Ident
open Zelus
open Aux

let p_handlers id handlers =
  List.map 
    (fun { p_cond; p_body = e; p_zero; p_env; p_loc } ->
      { p_cond; p_zero; p_env; p_loc;
        p_body = eq id e })
  handlers

let eq_and eq1 eq2 = Aux.eqmake (EQand [eq1; eq2])
let eq_der id e = Aux.eqmake (EQder { id; e; e0_opt = None; handlers = [] })

let present id e0_opt handlers eq_list =
  let else_branch =
    match e0_opt with
    | None -> NoDefault | Some(e0) -> eq_init id e0 in
  match handlers with
  | [] -> eq_list
  | _ ->
     let handlers = p_handlers id handlers in
     Aux.eq_make (EQpresent { handlers; default_opt }) :: eq_list

let der_present id e e0_opt handlers =
  let eq_list =
    match e0_opt with | None -> [] | Some(e0) -> [eq_init id e0] in
  present id e handlers eq_list

let equation funs acc eq =
  let { eq_desc }, acc = funs.equation acc eq in
  match eq_desc with
    | EQder { id; e; e_opt; handlers } ->
        eq_and (eq_der x e) (present id e0_opt handlers)
    | _ -> raise Mapfold.Fallback

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with
      equation; set_index; get_index } in
  let p, _ = Mapfold.program_it funs { empty with genv } p in
  p
