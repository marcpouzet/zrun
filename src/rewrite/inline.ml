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

(* inlining; this step assumes that static reduction is done already *)
(* this means that all variable defined at top level in declarations *)
(* are of the form [let x = e] where [x] is a value *)
(* a close term in head normal form *)
(* all function calls [inline f e1 ... en] are inlined *)

open Misc
open Location
open Zelus
open Ident
open Lident
open Defnames
open Genv
open Value
open Error
open Mapfold

(* the type of the accumulator *)
type acc =
  { genv : Value.pvalue Genv.genv;
    (* the global environment *)
    renaming : Ident.t Env.t;
    (* name to name environment *)
  }

let empty = { genv = Genv.empty; renaming = Env.empty }

(* Build a renaming from an environment *)
let build global_funs ({ renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }

let var_ident global_funs ({ renaming } as acc) x =
  try Env.find x renaming, acc with Not_found ->
    Debug.print_string "Inline: unbound identifier" (Ident.name x);
    x, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let pat x = { pat_desc = Evarpat(x); pat_loc = no_location; pat_info = no_info }

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
let local_in funs f_args arg_list acc { r_desc } =
  (* build a list of equations *)
  let eq_list = List.map2 eq_of_f_arg_arg f_args arg_list in
  let vardec_list =
    List.fold_left (fun acc vardec_list -> vardec_list @ acc) [] f_args in
  match r_desc with
  | Exp(e_r) ->
     let e_r, acc = funs.expression funs acc e_r in
     Aux.emake (Elocal(Aux.blockmake vardec_list eq_list, e_r)) no_info,
     acc
  | Returns { b_vars; b_body; b_write; b_env } ->
     let b_body, acc = funs.equation funs acc b_body in
     let vardec_list = b_vars @ vardec_list in
     let eq_list = b_body :: eq_list in
     Aux.emake
       (Elocal(Aux.blockmake vardec_list eq_list,
               returns_of_vardec_list b_vars)) no_info,
     acc

(** Expressions *)
let expression funs ({ genv } as acc) e = 
  let e, acc = Mapfold.expression funs acc e in
  match e.e_desc with
  | Eapp { is_inline = true;
           f = { e_desc = Eglobal { lname }; e_loc = f_loc }; arg_list } ->
     let { Genv.info } = Genv.find lname genv in
     begin match info with
     | Vclosure
       { c_funexp = { f_args; f_body }; c_genv } ->
        let e, acc =
          local_in funs f_args arg_list { acc with genv = c_genv } f_body in
        e, { acc with genv }
     | _ -> e, acc
     end
  | Eapp { f = { e_desc = Efun { f_args; f_body } }; arg_list } ->
     local_in funs f_args arg_list acc f_body
  | _ -> e, acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with expression; global_funs; set_index; get_index } in
  let p, _ = Mapfold.program_it funs { empty with genv } p in
  p

