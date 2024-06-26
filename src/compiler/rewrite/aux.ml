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
open Global
    
let desc e = e.desc
let make x = { desc = x; loc = no_location }

let emake desc info =
  { e_desc = desc; e_loc = no_location; e_info = info }
let pmake desc info =
  { pat_desc = desc; pat_loc = no_location; pat_info = info }
let eqmake w desc =
  { eq_desc = desc; eq_loc = no_location; eq_write = w }

let global lname = Eglobal { lname = lname }

let pat_make x =
  { pat_desc = Evarpat(x); pat_loc = no_location; pat_info = no_info }

let eq_make p e =
  let w = { Defnames.empty with dv = Write.fv_pat S.empty p } in
  eqmake w (EQeq(p, e))

let id_eq_make id e =
  let w = Defnames.singleton id in
  eqmake w (EQeq(pat_make id, e))

let eq_init_make id e =
  let eq = eqmake (Defnames.singleton id) (EQinit(id, e)) in
  let eq, _ = Write.equation eq in eq

let eq_der id e =
  let w = { Defnames.empty with der = S.singleton id } in
  eqmake w (EQder { id; e; e_opt = None; handlers = [] })

let eq_and_make eq1 eq2 =
  let w = Defnames.union eq1.eq_write eq2.eq_write in
  eqmake w (EQand [eq1; eq2])

let block_make vardec_list eq_list =
  let b_body =
    match eq_list with
    | [] -> eqmake Defnames.empty EQempty
    | [eq] -> eq
    | _ -> eqmake Defnames.empty (EQand(eq_list)) in
  let b = { b_vars = vardec_list; b_env = Env.empty; b_loc = no_location;
            b_write = Defnames.empty; b_body } in
  let b, _, _ = Write.block b in
  b

let pat_of_vardec_make { var_name } = pat_make var_name

let pat_of_vardec_list_make vardec_list =
  match vardec_list with
  | [] -> pmake Ewildpat Misc.no_info
  | _ -> pmake (Etuplepat(List.map pat_of_vardec_make vardec_list)) no_info

let eq_of_f_arg_arg_make f_arg arg =
  let p = pat_of_vardec_list_make f_arg in
  eq_make p arg

let returns_of_vardec_make { var_name } = emake (Evar(var_name)) no_info

let returns_of_vardec_list_make vardec_list =
  match vardec_list with
  | [] -> emake (Econst(Evoid)) no_info
  | _ -> emake (Etuple(List.map returns_of_vardec_make vardec_list)) no_info

(*
(* translate the internal representation of a type into a type definition *)
let type_decl_of_type_desc name ty_params size_params ty_decl =
  (* variant types *)
  let variant_type
      { qualid = qualid;
        info = { constr_arg = arg_l; constr_arity = arit } } =
    let desc =
      if arit = 0 then
        Econstr0decl(Genv.shortname qualid)
      else Econstr1decl(Genv.shortname qualid,
                        List.map type_expression_of_typ arg_l) in
    make desc in
  (* record types *)
  let record_type { qualid = qualid; info = { label_arg = arg } } =
    Genv.shortname qualid, type_expression_of_typ arg in

  let params = List.map (fun i -> "'a" ^ (string_of_int i)) ty_param in
  let type_decl_desc =
    match ty_desc with
      | Abstract_type -> Eabstract_type
      | Variant_type(c_list) -> Evariant_type(List.map variant_type c_list)
      | Record_type(l_list) -> Erecord_type(List.map record_type l_list)
      | Abbrev(_, ty) -> Eabbrev(type_expression_of_typ ty) in
  (tyname, params, make type_decl_desc)
*)
