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

(* This pass is necessary for static scheduling. *)
(* For every local variable [x] such that [last x] is used *)
(* add an equation [lx = last* x] and replace [last x] by [lx] *)
(* For input variables (functions and patterns), they are treated by *)
(* an other pass *)

(*
  Example:

  local (last x), (last y), z init e
  do init x = v0 and init y = v1 and ... y = last x + 1 and
  ... x = last y + 1 and ... z ...

  is rewritten:

  local lx, (last x), ly, (last y) do
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
  { locals: Misc.no_info Env.t; (* names that are defined locally in a block *)
    renaming: Ident.t Env.t; (* for some of these names, associate [lx] to [x] *)
  }

let empty = { locals = Env.empty; renaming = Env.empty }

(* Make an equation [lx = last* x] *)
let add_eq_copy l_renaming =
  let copy lx x = Aux.id_eq lx (Aux.last_star x) in
  Env.fold (fun x lx acc -> copy lx x :: acc) l_renaming []

let update_env l_env l_renaming =
  Env.fold (fun x lx acc -> Env.add lx Misc.no_info acc) l_renaming l_env

(* update a local declaration [local (last x)...] into [local lx, (last x)...] *)
let update_vardec_list b_vars l_renaming =
  List.fold_left
    (fun acc ({ var_name } as v) ->
      try let lx = Env.find var_name l_renaming in
          Aux.vardec lx false None None :: { v with var_is_last = true } :: acc
      with
      | Not_found -> v :: acc) [] b_vars

(* split [renaming] in two according to [l_env]. Returns [l_renaming] *)
(* and [r_renaming] such that [renaming = l_renaming + r_renaming] *)
(* and [Names(l_renaming) subset Names(l_env)] *)
let split l_env renaming =
  Env.fold
    (fun x lx (l_renaming, r_renaming) ->
       if Env.mem x l_env then Env.add x lx l_renaming, r_renaming
       else l_renaming, Env.add x lx r_renaming)
    renaming (Env.empty, Env.empty)
    
let intro ({ locals; renaming } as acc) id =
  try
    let lx = Env.find id renaming in lx, acc
  with
  | Not_found ->
    if Env.mem id locals then
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

(* add extra equations [lx = last* x] *)
let leq_t funs ({ locals } as acc) ({ l_eq; l_env } as leq) =
  let l_eq, { renaming } =
    Mapfold.equation
      funs { acc with locals = Env.append l_env locals } l_eq in
  (* add an equation [lx = last* x] for every [x\lx] in [renaming inter l_env] *)
  let l_renaming, renaming = split l_env renaming in
  { leq with l_eq = Aux.par (l_eq :: add_eq_copy l_renaming);
             l_env = update_env l_env l_renaming; l_rec = true },
  { locals; renaming }

(* add extra equations [lx = last* x] *)
let block funs acc ({ b_vars; b_body; b_env } as b) =
  let b_vars, ({ locals } as acc) =
    Util.mapfold (Mapfold.vardec funs) acc b_vars in
  let b_body, ({ renaming } as acc) =
    Mapfold.equation funs { acc with locals = Env.append b_env locals } b_body in
  let l_renaming, renaming = split b_env renaming in
  let b_body = Aux.par (b_body :: add_eq_copy l_renaming) in
  { b with b_vars = update_vardec_list b_vars l_renaming;
           b_env = update_env b_env l_renaming;
           b_body }, { locals; renaming }

(* the inputs/outputs must be unchanged *)
let funexp funs acc ({ f_body = { r_desc } as r } as f) =
  let r_desc, acc =
    match r_desc with
    | Exp(e) ->
       let e, acc = Mapfold.expression funs acc e in Exp(e), acc
    | Returns(b) ->
       let b, acc = Mapfold.block funs acc b in Returns(b), acc in
  { f with f_body = { r with r_desc } }, acc

let pattern funs acc p = p, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; leq_t; block; funexp; pattern;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
