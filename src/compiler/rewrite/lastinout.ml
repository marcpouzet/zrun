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

(* All variables in patterns must be values only                           *)
(* e.g., variables in function parameters, variables in patterns, etc.     *)
(* Any expression [last x] where [x] is expected to be a value             *)
(* is rewritten [last* m and m = x] are introduced *)

(* Example:
 *- [let node f(x) = ... last x...] is rewritten
 *- [let node f(x) = local (last m), r do r = ... last* m and m = x in r]
 *- [let node f(x) returns (...y...) ...last x... last y ...] is rewritten
 *- [let node f(x) returns (...y...) ... last* m ... last* my ... m = x ... my = y]
 *- [match e with P(...x...) -> ...last x...] is rewritten
 *- [match e with P(...x...) -> local (last m) ...last* m... and m = x]
 *- [present e(...x...) -> ... last x ...] is rewritten
 *- [present e(...x...) -> local (last m) do r = ... last* m and m = x in r]
 *- [present e(...x...) -> ... last x ...] is rewritten
 *- [present e(...x...) -> local (last m) ... last* m and m = x]
 *)

open Location
open Zelus
open Ident
open Aux

(* renaming(x) = m for [x] in [in/out names] *)
type acc =
  { inout: Misc.no_info Env.t; (* names in inputs/outputs *)
    renaming: Ident.t Env.t; (* for some of these names, associate [m] to [x] *)
  }

let empty = { inout = Env.empty; renaming = Env.empty }

(* Make an equation [lx = last* x] *)
let add_eq_copy l_renaming acc =
  let copy m x = Aux.id_eq m (Aux.var x) in
  Env.fold (fun x m acc -> copy m x :: acc) l_renaming acc

let update_env l_env l_renaming =
  Env.fold (fun x m acc -> Env.add m Misc.no_info acc) l_renaming l_env

(* add extra local declarations *)
let vardec_list l_renaming acc =
  Env.fold (fun x m acc -> Aux.vardec m true None None :: acc) l_renaming acc

(* split [renaming] in two according to [l_env]. Returns [l_renaming] *)
(* and [r_renaming] such that [renaming = l_renaming + r_renaming] *)
(* and [Names(l_renaming) subset Names(l_env)] *)
let split l_env renaming =
  Env.fold
    (fun x lx (l_renaming, r_renaming) ->
       if Env.mem x l_env then Env.add x lx l_renaming, r_renaming
       else l_renaming, Env.add x lx r_renaming)
    renaming (Env.empty, Env.empty)
 
let intro ({ inout; renaming } as acc) id =
  try
    let m = Env.find id renaming in m, acc
  with
  | Not_found ->
    if Env.mem id inout then
      let m = fresh "m" in m, { acc with renaming = Env.add id m renaming }
    else id, acc

(* add entries in the environment *)
let build funs ({ inout } as acc) env = env, { acc with inout = env }

(* replace [last id] by [last*m] *)
let last_ident _ acc { copy; id } =
  let m, acc = intro acc id in
  { copy = false; id = m }, acc

(* replace [init id = e] by [init m = e] *)
let init_ident _ acc id = intro acc id

let funexp funs ({ inout } as acc) ({ f_body = { r_desc } as r; f_env } as f) =
  let e_local l_renaming e =
    if Env.is_empty l_renaming then e
    else
      let r = fresh "r" in
      Aux.e_local
        (Aux.block_make
           (Aux.vardec r false None None :: vardec_list l_renaming [])
           (add_eq_copy l_renaming [Aux.id_eq r e])) (var r) in
  match r_desc with
    | Exp(e) ->
      let e, ({ renaming } as acc) =
        Mapfold.expression funs { acc with inout = Env.append f_env inout } e in
       let l_renaming, renaming = split f_env renaming in
       Exp(e_local l_renaming e), { acc with renaming }
    | Returns({ b_vars; b_body; b_env } as b) ->
      (* the interface must not be changed *)
      let b_vars, ({ inout } as acc) =
        Util.mapfold (Mapfold.vardec funs) acc b_vars in
      let b_body, ({ renaming } as acc) =
        Mapfold.equation funs
          { acc with inout = Env.append f_env (Env.append b_env inout) } b_body in
      let b_renaming, renaming = split b_env renaming in
      let f_renaming, renaming = split f_env renaming in
      let b_body =
        Aux.eq_local_vardec
          (vardec_list b_renaming (vardec_list f_renaming []))
          (add_eq_copy b_renaming (add_eq_copy l_renaming [b_body])) in
      Returns { b with b_vars; b_body = b; b_env },
      { acc in
  { f with f_body = { r with r_desc } }, acc

and leq_t funs acc ({ l_eq; l_env } as leq) =
  (* for every entry [x\m] in [acc] that appear in [l_env] *)
  (* add an equation [m = x]; update [l_env] and [l_eq.eq_write] *)
  (* returns the remaining [acc] *)
  let l_eq, acc = Mapfold.equation funs acc l_eq in
  let renaming_list, acc = remove l_env acc in
  { leq with l_eq = Aux.par (l_eq :: eq_copy_names renaming_list);
             l_env = update_env l_env renaming_list }, acc

and block funs acc b =
  let { b_vars; b_body; b_env; b_write } as b, acc = Mapfold.block funs acc b in
  (* for every entry [x\m] in [acc] that appear in [b_env] *)
  (* add an equation [m = x]; update [b_env] and [b_write] *)
  (* returns the remaining [acc] *)
  let b_vars, acc = 
    Util.mapfold (Mapfold.vardec funs) acc b_vars in
  let b_body, acc = Mapfold.equation funs acc b_body in
  let renaming_list, acc = remove b_env acc in
  let b_body = Aux.par (b_body :: eq_copy_names renaming_list) in
  { b with b_vars = update_vardec_list b_vars renaming_list;
           b_env = update_env b.b_env renaming_list;
           b_body }, acc
									  
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs =
    { Mapfold.default_global_funs with last_ident; init_ident } in
  let funs =
    { Mapfold.defaults with leq_t; block; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs Env.empty p in
  { p with p_impl_list = p_impl_list }

(*


                              if copy then
    try (* if [id] is already in [acc] and associated to [m] *)
      (* replace [last id] by [last*m] *)
      let m = Env.find id acc in
      { copy = false; id = m }, acc
    with
    | Not_found ->
       let m = fresh "m" in
       { copy = false; id = m }, Env.add id m acc
  else l, acc *)


