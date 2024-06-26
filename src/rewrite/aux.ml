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

(* Functions to build terms *)
(* Invariant: writes (variables defined an equation) must be correct *)

open Misc
open Location
open Zelus
open Ident
open Lident

let desc e = e.desc
let make x = { desc = x; loc = no_location }

let emake desc info =
  { e_desc = desc; e_loc = no_location; e_info = info }
let pmake desc info =
  { pat_desc = desc; pat_loc = no_location; pat_info = info }
let eqmake desc =
  { eq_desc = desc; eq_loc = no_location; eq_write = Defnames.empty }

let global lname = Eglobal { lname = lname }

let blockmake vardec_list eq_list =
  let b_body =
    match eq_list with
    | [] -> eqmake EQempty
    | [eq] -> eq
    | _ -> eqmake (EQand(eq_list)) in
  let b = { b_vars = vardec_list; b_env = Env.empty; b_loc = no_location;
            b_write = Defnames.empty; b_body } in
  let b, _, _ = Write.block b in
  b

let pat x = { pat_desc = Evarpat(x); pat_loc = no_location; pat_info = no_info }

let pat_of_vardec { var_name } = pat var_name

let pat_of_vardec_list vardec_list =
  match vardec_list with
  | [] -> pmake Ewildpat Misc.no_info
  | _ -> pmake (Etuplepat(List.map pat_of_vardec vardec_list)) no_info

let eq_of_f_arg_arg f_arg arg =
  let p = pat_of_vardec_list f_arg in
  eqmake (EQeq(p, arg))

let returns_of_vardec { var_name } = emake (Evar(var_name)) no_info

let returns_of_vardec_list vardec_list =
  match vardec_list with
  | [] -> emake (Econst(Evoid)) no_info
  | _ -> emake (Etuple(List.map returns_of_vardec vardec_list)) no_info
 
