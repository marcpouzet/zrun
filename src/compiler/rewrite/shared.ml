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

let empty = S.empty

(* Makes a copy of a pattern [p] when it contains a shared variable [x] *)
(* introduce auxilary equations [x = x_copy] for every name in [dv] *)
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

let pattern funs acc p = p, acc
                         
(* [dv] is the set of names possibly written in [eq] and shared, that is *)
(* they appear on at least one branch of a conditional *)
let equation funs acc eq =
  let { eq_desc; eq_write } as eq, acc = Mapfold.equation funs acc eq in
  match eq_desc with
  | EQeq(p, e) ->
     copy_pattern acc p e, acc
  | EQif { e; eq_true; eq_false } ->
    let e, acc = Mapfold.expression funs acc e in
    let eq_true, acc = equation funs eq_write.dv eq_true in
    let eq_false, acc = equation funs eq_write.dv eq_false in
    { eq with eq_desc = EQif {e; eq_true; eq_false } }, acc
  | EQmatch({ e; handlers } as m) ->
     (* compute the set of shared variables; those that a written in one *)
     (* branch *)
     let body acc ({ m_body } as m_h) =
       let m_body, acc = Mapfold.equation funs acc m_body in
       { m_h with m_body }, acc in
     let e, acc = Mapfold.expression funs acc e in
     let handlers, acc =
       Util.mapfold body eq_write.dv handlers in
       { eq with eq_desc = EQmatch { m with e; handlers } }, acc
  | EQlet(leq, eq_let) ->
     eq, acc
  | _ -> eq, acc

and block funs acc ({ b_body } as b) =
  let b_body, acc = Mapfold.equation funs acc b_body in
  { b with b_body }, acc
    
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; block;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs S.empty p in
  { p with p_impl_list = p_impl_list }
