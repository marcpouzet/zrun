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

(* static inlining; warning: this step must be done after static reduction *)
(* function calls [inline f e1 ... en] are inlined *)

open Misc
open Location
open Ast
open Ident
open Lident
open Defnames
open Genv
open Value
open Error
open Mapfold

let fresh () = Ident.fresh "inline"

(* the type of the accumulator *)
type acc = { genv : Value.pvalue Genv.genv }

let empty = { genv = Genv.empty }

let pat x = 
    { pat_desc = Evarpat(x); pat_loc = no_location; pat_info = no_info }

let pat_of_vardec { var_name } = pat var_name

let pat_of_vardec_list vardec_list =
  match vardec_list with
  | [] -> Aux.pmake Ewildpat Misc.no_info
  | _ -> Aux.pmake (Etuplepat(List.map pat_of_vardec vardec_list)) no_info

let eq_of_f_arg_arg f_arg arg =
  let p = pat_of_vardec_list f_arg in
  let dv = Write.fv_pat S.empty p in
  Aux.eqmake { Defnames.empty with dv } (EQeq(p, arg))

let returns_of_vardec { var_name } = Aux.emake (Evar(var_name)) no_info

let returns_of_vardec_list vardec_list =
  match vardec_list with
  | [] -> Aux.emake (Econst(Evoid)) no_info
  | _ -> Aux.emake (Etuple(List.map returns_of_vardec vardec_list)) no_info
  
(** Main transformation *)
(* [(\v_list1 ... v_listn. e) e1 ... en] 
 *- rewrites to:
 *- [local v_list1,...,v_listn do p1 = e1 ... pn = en in e]
 *- [(\(v_list1 ... v_listn. v_ret eq) e1 ... en
 *- rewrites to:
 *- [local v_list1,...,v_listn, v_ret
 *-  do p1 = e1 ... pn = en and eq in p_v *)
let local_in f_args arg_list { r_desc } =
  (* build a list of equations *)
  let eq_list = List.map2 eq_of_f_arg_arg f_args arg_list in
  let vardec_list =
    List.fold_left (fun acc vardec_list -> vardec_list @ acc) [] f_args in
  match r_desc with
  | Exp(e_r) ->
     Aux.emake (Elocal(Aux.blockmake vardec_list eq_list, e_r)) no_info
  | Returns { b_vars; b_body; b_write; b_env } ->
     let vardec_list = b_vars @ vardec_list in
     let eq_list = b_body :: eq_list in
     Aux.emake
       (Elocal(Aux.blockmake vardec_list eq_list,
               returns_of_vardec_list b_vars)) no_info

(** Expressions *)
let expression funs acc e = 
  let e, acc = Mapfold.expression funs acc e in
  match e.e_desc with
  | Eapp { is_inline = true;
           f = { e_desc = Eglobal { lname }; e_loc = f_loc }; arg_list } ->
     let { Genv.info } = Genv.find lname acc.genv in
     begin match info with
     | Vclosure
       { c_funexp = { f_args; f_body }; c_genv; c_env } ->
        let e = local_in f_args arg_list f_body in e, acc
     | _ -> e, acc
     end
  | Eapp { f = { e_desc = Efun { f_args; f_body } }; arg_list } ->
     let e = local_in f_args arg_list f_body in e, acc
  | _ -> e, acc

let block funs acc b = b, acc

let program p =
  let funs =
    { Mapfold.defaults with expression; block } in
  let p, acc = Mapfold.program funs empty p in
  p

