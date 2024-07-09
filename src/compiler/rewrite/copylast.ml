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
(* by [lx] *)
(* This step is necessary for static scheduling. *)

(*
  Example:

  local (last x), (last y), z init e
  do init x = v0 and init y = v1 and ... y = last x + 1 and
  ... x = last y + 1 and ... z ...

  is rewritten:

  local (last x), (last y), lx, ly do
  init x = v0 and init y = v1
  ly = last* y
  lx = last* x
  y = lx + 1
  x = ly + 1
*)

open Location
open Zelus
open Ident
open Aux

(* renaming(x) = lx for [x] in [out_names] *)
type acc =
  { def_names: Misc.no_info Env.t; (* names that are defined locally in a block *)
    renaming: Ident.t Env.t; (* for some of these names, associate [lx] to [x] *)
  }
  
(* Make an equation [lx = last* x] *)
let eq_copy x lx = Aux.id_eq lx (Aux.last_star x)

(* partition a renaming in two *)
let split l_env renaming =
  Env.fold
    (fun x lx (l_renaming, renaming) ->
       if Env.mem x l_env then Env.add x lx l_renaming, renaming
       else l_renaming, Env.add x lx renaming)
    renaming (Env.empty, Env.empty)
    
let eq_copy_names l_renaming =
  Env.fold (fun x lx acc -> eq_copy x lx :: acc) l_renaming

let update_env l_env l_renaming =
  Env.fold
    (fun x m acc -> Env.add m Misc.no_info acc) l_renaming l_env
    
(* an entry [local x [init e] [default v]] becomes [local m [init e] [default v] *)
(* and an extra entry [local x] is added *)
let update_vardec_list b_vars renaming_list =
  List.fold_left
    (fun acc (_, m) -> Aux.vardec m true None None :: acc) 
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

let intro ({ def_names; renaming } as acc) id =
  try
    let lx = Env.find id renaming in
    lx, acc
  with
  | Not_found ->
    if S.mem id def_names then
      let lx = fresh "lx" in lx, { acc with renaming = Env.add id lx renaming }
    else id, acc
                                             
(* replace every occurrence of [last x] where [x] is a local variable *)
(* by [lx]; an equation [lx = last*x] will be added *)
let expression funs acc ({ e_desc } as e) =
  match e_desc with
  | Elast { copy; id } ->
    if copy then
      (* turn [last x] into [lx] *)
      let lx, acc = intro acc id in var lx, acc
    else e, acc
  | _ -> raise Mapfold.Fallback

let rec funexp funs acc ({ f_body = { r_desc } as r } as f) =
  let r_desc, acc =
    match r_desc with
    | Exp(e) ->
       let e, acc = Mapfold.expression funs acc e in
       Exp(e)
    | Returns b ->
       let b, acc = block funs acc b in
       Returns b, acc in
  { f with f_body = { r with r_desc } }, acc

and leq_t funs ({ def_names } as acc) ({ l_eq; l_env } as leq) =
  let l_eq, ({ renaming } as acc) =
    Mapfold.equation
      funs { acc with def_names = Env.append l_env def_names } l_eq in
  (* add equations [lx = last* x] for every [x\lx] in [renaming] *)
  (* which is also in [l_env] *)
  { leq with l_eq = Aux.par (l_eq :: eq_copy_names l_env renaming);
             l_env = update_env l_env renaming },
  { acc with def_names }

(* for every entry [x\m] in [acc] that appear in [b_env] *)
(* add an equation [m = x]; update [b_env] and [b_write] *)
(* returns the remaining [acc] *)
and block funs acc ({ b_vars; b_body; b_env; b_write } as b) =
  Mapfold.block funs acc b in
  
  let b_vars, acc =  Util.mapfold (Mapfold.vardec funs) acc b_vars in
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


