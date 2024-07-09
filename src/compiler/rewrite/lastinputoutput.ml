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

(* Add an equation [m = x] every time [last x] is used; replace [last x] *)
(* by [last*m] and rename [init x = e] in [init m = e] *)
(* This step is necessary for static scheduling. *)

(*
  Example:

  fun x -> last x + 1

  is rewritten:

  fun x -> local (last m) do m = x and y = last*m + 1 in y

  fun x returns (o, y) ... last y ...

  is rewritten:

  fun x returns (o, y) local m ... last* m ... and m = y

  local x, y, z init e
  do init x = v0 and init y = v1 and y = last x + 1 and x = last y + 1 and ... z ...

  is rewritten:

  local x, y, mx, my, z init e do
  init mx = v0 and init my = v1
  y = last* mx + 1
  x = last* my + 1
  mx = x
  my = y and ...

  An alternative would be:

  local (last x), (last y), lx, ly do
  init x = v0 and init y = v1
  ly = last* y
  lx = last* x
  y = lx + 1
  x = ly + 1

  The difference in efficiency between the two is not clear; it depdends
  on how CSE/Tomato steps are done after. The first ensures
  that the kind of variables is unchanged. In particular, it can be applied
  to variables that are input and outputs of functions. After this step, they
  are not required to be state variables. 
*)

open Location
open Zelus
open Ident
open Aux

type acc = Ident.t Env.t (* associate names to names *)

(* Make an equation [m = x] *)
let eq_copy (x, m) = Aux.id_eq m (Aux.var x)

let eq_copy_names renaming_list = List.map eq_copy renaming_list

let update_env l_env renaming_list =
  List.fold_left 
    (fun acc (x, m) -> Env.add m Misc.no_info acc) l_env renaming_list

(* an entry [local x [init e] [default v]] becomes [local m [init e] [default v] *)
(* and an extra entry [local x] is added *)
let update_vardec_list b_vars ming_list =
  List.fold_left
    (fun v_list ({ var_name } as v) ->
       try Aux.vardec x false None None;(_, m) -> Aux.vardec m true None None :: acc) 
    b_vars renaming_list

(* [remove l_env acc = renaming, acc'] extract entries in [acc] from [l_env] *)
let remove l_env acc =
  Env.fold
    (fun x _ (renaming_list, acc) ->
       try
         let m = Env.find x acc in
         (x, m) :: renaming_list, Env.remove x acc
       with Not_found -> renaming_list, acc)
    l_env ([], acc)

(* introduce a fresh copy [m] for [id] *)
let intro acc id =
  try
    let m = Env.find id acc in m, acc
  with
  | Not_found -> let m = fresh "m" in m, Env.add id m acc

(* replace [last id] by [last*m] *)
let last_ident _ acc { copy; id } =
  let m, acc = intro acc id in
  { copy = false; id = m }, acc

(* replace [init id = e] by [init m = e] *)
let init_ident _ acc id = intro acc id

let rec funexp funs acc ({ f_body = { r_desc } as r; f_env } as f) =
  let r_desc, acc =
    match r_desc with
    | Exp(e) ->
       let e, acc = Mapfold.expression funs acc e in
       let renaming_list, acc = remove f_env acc in
       let vardec_list = update_vardec_list [] renaming_list in
       Exp(Aux.e_local (Aux.block_make vardec_list
                          (eq_copy_names renaming_list)) e), acc
    | Returns b ->
       let b, acc = block funs acc b in
       Returns b, acc in
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


