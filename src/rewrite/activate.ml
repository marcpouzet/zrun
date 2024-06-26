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

(* removing equations [der x = e init e0 reset z1 -> e1 | ... | zn -> en] *)

open Misc
open Location
open Ident
open Zelus
open Aux

(* An equation: [der x = e1 init e0 reset z1 -> e1 | ... | zn -> en] *)
(* is rewritten *)
(* [init x = e0 and present z1 -> x = e1 | ... else der x = e] *)

let block_of_eq s pat e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQeq(pat, e))]; 
    b_loc = no_location; b_write = { Deftypes.empty with dv = s };
    b_env = Env.empty }

let block_of_der s x e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQder(x, e, None, []))]; 
    b_loc = no_location; 
    b_write = { Deftypes.empty with der = s }; b_env = Env.empty }
    
let block_spat_e_list s pat spat_e_list =
  List.map 
    (fun { p_cond = spat; p_body = e; p_env = env; p_zero = zero } ->
      { p_cond = spat;
        p_body = block_of_eq s pat e;
        p_env = env; p_zero = zero }) spat_e_list

let present id e handlers eq_list =
  let spat_b_list =
    block_spat_e_list s (varpat x Initial.typ_float) spat_e_list in
  (* only generate a present if [spat_b_list] is not empty *)
  match handlers with
  | [] -> (eq_der id e) :: eq_list
  | _ ->
     let handlers = eq_of_handlers id handlers in
     let default_opt = Else(eq_der id e) in
     (eqmake (EQpresent { handlers; default_opt })) :: eq_list

let der_present id e e0_opt handlers =
  let eq_list =
    match e0_opt with | None -> [] | Some(e0) -> [eq_init id e0] in
  present id e handlers eq_list

let equation funs acc eq =
  let { eq_desc }, acc = funs.equation acc eq in
  match eq_desc with
    | EQder { id; e; e_opt; handlers } ->
        der_present id e e0_opt handlers
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
