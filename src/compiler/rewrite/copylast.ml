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
(* by [last* m]. This step is necessary for static scheduling *)

open Location
open Zelus
open Ident
open Aux

type acc = Ident.t Env.t (* associate names to names *)

(* Make an equation [m = x] *)
let eq_copy (x, m) = Aux.id_eq m (Aux.var x)

let eq_copy_names renaming_list = List.map eq_copy renaming_list

let add_env l_env renaming_list =
  List.fold_left (fun acc (x, m) -> Env.add m Misc.no_info acc) l_env renaming_list

let add_vardec_list b_vars renaming_list =
  List.fold_left
    (fun acc (_, m) -> Aux.vardec m false None None :: acc) b_vars renaming_list

(* [remove l_env acc = renaming, acc'] extract entries in [acc] from [l_env] *)
let remove l_env acc =
  Env.fold
    (fun x _ (renaming_list, acc) ->
       try
         let m = Env.find x acc in
         (x, m) :: renaming_list, Env.remove x acc
       with Not_found -> renaming_list, acc)
    l_env ([], acc)


(* replace occurrences of [last x] by [lx] *)
let rec expression funs acc e =
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  let e_desc, acc = match e_desc with
    | Elast { copy; id } ->
       if copy then
         try (* if [id] is already in [acc] an associated to [m] *)
           (* replace [last id] by [last*m] *)
           let m = Env.find id acc in
           Elast { copy = false; id = m }, acc
         with Not_found ->
           let m = fresh "m" in
           Elast { copy = false; id = m }, Env.add id m acc
       else e_desc, acc
    | Efun(f) ->
       let f, acc = funexp funs acc f in Efun(f), acc
    | Elet(l, e_result) ->
       let l, acc = leq_t funs acc l in
       let e_result, acc = expression funs acc e_result in
       Elet(l, e_result), acc
    | _ -> raise Mapfold.Fallback in
  { e with e_desc }, acc

and funexp funs acc ({ f_body = { r_desc } as r; f_env } as f) =
  let r_desc, acc =
    match r_desc with
    | Exp(e) ->
       let e, acc = expression funs acc e in
       let renaming_list, acc = remove f_env acc in
       let vardec_list = add_vardec_list [] renaming_list in
       Exp(Aux.e_local (Aux.block_make vardec_list
                          (eq_copy_names renaming_list)) e), acc
  | Returns b ->
     let b, acc = block funs acc b in
     Returns b, acc in
  { f with f_body = { r with r_desc } }, acc

and leq_t funs acc leq =
  let { l_eq; l_env } as leq, acc = Mapfold.leq_t funs acc leq in
  (* for every entry [x\m] in [acc] that appear in [l_env] *)
  (* add an equation [m = x]; update [l_env] and [l_eq.eq_write] *)
  (* returns the remaining [acc] *)
  let renaming_list, acc = remove l_env acc in
  { leq with l_eq = Aux.par (l_eq :: eq_copy_names renaming_list);
             l_env = add_env l_env renaming_list }, acc

and block funs acc b =
  let { b_vars; b_body; b_env; b_write } as b, acc = Mapfold.block funs acc b in
  (* for every entry [x\m] in [acc] that appear in [b_env] *)
  (* add an equation [m = x]; update [b_env] and [b_write] *)
  (* returns the remaining [acc] *)
  let renaming_list, acc = remove b_env acc in
  { b with b_vars = add_vardec_list b_vars renaming_list;
           b_env = add_env b.b_env renaming_list;
           b_body = Aux.par (b_body :: eq_copy_names renaming_list) }, acc

(* Translation of equations. *)
and equation funs acc eq =
  let { eq_desc }, acc = Mapfold.equation funs acc eq in
  let eq_desc, acc = match eq_desc with
    | EQlocal(b) ->
       let b, acc = block funs acc b in
       EQlocal(b), acc
    | EQlet(l, eq) ->
       let l, acc = leq_t funs acc l in
       let eq, acc = equation funs acc eq in
       EQlet(l, eq), acc
    | _ -> raise Mapfold.Fallback in
  { eq with eq_desc }, acc
									  
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; leq_t; block; equation;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs Env.empty p in
  { p with p_impl_list = p_impl_list }