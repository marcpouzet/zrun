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

(* removes the initialization operator [e1 -> e2] *)
(* This operator is equivalent to [if (true fby false) then e1 else e2] *)
(* that is [if last i then e1 else e2] with [init i = true and i = false] *)
(* An initialization register [i] with [init i = true and i = false] *)
(* is introduced for every control block *)

open Misc
open Location
open Ident
open Zelus
open Mapfold

(*
  [reset
   ... init x = e ... (* [e] is static *)
   every z]

  is unchanged

  [reset
   ... init x = e ... (* [e] is not static *)
   every z

   is rewritten:

   reset
   ... local i init and i = false and reset init x = e every last i
   every z] is unchanged

   match e with
   | P1 -> eq1 | ... | Pn -> eqn

   is rewritten:

   match e with
   | P1 -> local i1 init true and i1 = false and eq1
   | ...
   | Pn -> local in init true and in = false and eqn
*)

(* Static expressions - simple sufficient condition for [e] to be static *)
let rec static { e_desc = desc } =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> true
  | Etuple(e_list) -> List.for_all static e_list
  | Erecord(qual_e_list) ->
     List.for_all (fun { arg } -> static arg) qual_e_list
  | Erecord_access { arg } -> static arg
  | _ -> false

type acc = { i: Ident.t; } (* the initialization variable *)

(* Surround an equation by a reset *)
let reset_init i eq = Aux.eq_reset eq (Aux.last i)

(* Introduce a block [local i init true do i = false and eq] *)
let intro_init_eq_local i eq =
  Aux.eq_local (Aux.block_make [Aux.vardec i false (Some(Aux.etrue)) None]
                  [Aux.eq_and (Aux.id_eq i Aux.efalse) eq])

(* Introduce a block [local m, i init true do m = last i and i = false in e] *)
let intro_init_e_local i e =
  let m = fresh "m" in
  Aux.e_local (Aux.block_make [Aux.vardec m false None None;
                               Aux.vardec i false (Some(Aux.etrue)) None]
                 [Aux.id_eq m (Aux.last i); Aux.id_eq i (Aux.efalse)]) e

(* Equations *)
let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQmatch { e; handlers } ->
     let body acc ({ m_body } as m_h) =
       (* introduce one init per branch *)
       let i = Ident.fresh "i" in
       let m_body, _ = funs.equation funs { i } m_body in
       { m_h with m_body = intro_init_eq_local i m_body }, acc in
     let e, acc = funs.expression funs acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
       { eq with eq_desc = EQmatch { is_total = true; e; handlers } }, acc
  | _ -> raise Mapfold.Fallback

(** Expressions. *)
let expression funs ({ i } as acc) ({ e_desc } as e) =
  let e_desc, acc = match e_desc with
  | Eop(Eminusgreater, [e1; e2]) ->
     let e1, acc = funs.expression funs acc e1 in
     let e2, acc = funs.expression funs acc e2 in
     (* [if last i then e1 else e2] *)
     Eop(Eifthenelse, [Aux.last i; e1; e2]), acc
    | Ematch({ e; handlers } as m) ->
       let body acc ({ m_body } as m_h) =
       (* introduce one init per branch *)
       let i = Ident.fresh "i" in
       let m_body, _ = funs.expression funs { i } m_body in
       { m_h with m_body = intro_init_e_local i m_body }, acc in
     let e, acc = funs.expression funs acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
     Ematch { m with e; handlers }, acc
    | _ -> e_desc, acc in
  { e with e_desc }, acc
 
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs { i = Ident.fresh "i" } p in
  { p with p_impl_list = p_impl_list }

