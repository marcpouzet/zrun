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

(* Identify assignments to shared variables *)
(* After this transformation, equations on structured patterns *)
(* like [pat = e] are such that no variable in [pat] *)
(* is shared nor a memory. All equations on those variables *)
(* are then of the form [x = e] *)

open Location
open Ident
open Zelus
open Aux
open Mapfold

(* An equation [pat = e] where [xi in pat] is shared is rewritten into *)
(* [local x_copyi,... do pat_copy = e and xi = x_copyi and ...] *)


let fresh () = Ident.fresh "copy"

(*
(* Computes the set of shared memories and state variables. *)
(* add them to [dv] *)
let shared dv l_env =
  let add x sort acc =
    match sort with | Sstatic | Sval -> acc | Svar _ | Smem _ -> S.add x acc in
  Env.fold (fun x { t_sort = sort } acc -> add x sort acc) l_env dv
    
(* Remove the flag [is_copy] from a environment of copies *)
let remove_is_copy copies =
  Env.map (fun (x_copy, _, ty) -> (x_copy, false, ty)) copies

(* Makes a list of copy equations [x = x_copy] for every entry in [env] *)
(* when the [is_copy] flag is true *)
let add_equations_for_copies eq_list copies =
  (* makes a value for [x_copy] *)
  Env.fold
    (fun x (x_copy, is_copy, ty) acc ->
     if is_copy then
       (eqmake (EQeq(varpat x ty, var x_copy ty))) :: acc
     else acc) copies eq_list

(* Extends the local environment with definitions for the [x_copy] *)
let add_locals_for_copies n_list n_env copies =
  let value ty = { t_sort = Deftypes.value; t_typ = ty } in
  let n_env =
    Env.fold
      (fun x (x_copy, _, ty) acc ->
       Env.add x_copy (value ty) acc) copies n_env in
  let n_copy_list =
    Env.fold
      (fun _ (x_copy, _, ty) acc ->
       (Zaux.vardec_from_entry x_copy { t_sort = Sval; t_typ = ty }) :: acc)
      copies n_list in
  n_copy_list, n_env
 *)


(* Makes a copy of a pattern if it contains a shared variable [x] *)
(* introduce auxilary equations [x = x_copy] in [copies] for every name *)
(* in [dv] *)
let copy_pattern dv p e =
  let var_ident global_funs ((dv, env) as acc) x =
    if S.mem x dv then if Env.mem x env then Env.find x env, acc
                       else let x_copy = fresh () in
                            x_copy, (dv, Env.add x x_copy env)
    else x, acc in
  let global_funs = { Mapfold.default_global_funs with var_ident } in
  let funs = { Mapfold.defaults with global_funs } in
  let p, (_, env) = Mapfold.pattern funs (dv, Env.empty) p in
  let vardec_list, x_x_copy_list =
    Env.fold
      (fun x x_copy (vardec_list, x_x_copy_list) ->
        Aux.vardec x_copy false None None :: vardec_list,
        Aux.id_eq x (Aux.var x_copy) :: x_x_copy_list) env ([], []) in
  Aux.eq_local_vardec
    vardec_list (Aux.eq_make p e :: x_x_copy_list)

(* [dv] is the set of names possibly written in [eq] which are shared, that is *)
(* they appear on at least of branch of a conditional *)
let equation funs acc eq =
  let { eq_desc } as eq, acc = Mapfold.equation funs acc eq in
  match eq_desc with
  | EQeq(p, e) ->
     copy_pattern acc p e, acc
  | EQmatch({ handlers }) ->
     eq, acc
  | EQlet(leq, eq_let) ->
     eq, acc
  | _ -> raise Mapfold.Fallback

let expression funs acc e =
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Elocal(b, e_local) ->
     e, acc
  | _ -> raise Mapfold.Fallback
    
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; expression;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs S.empty p in
  { p with p_impl_list = p_impl_list }
