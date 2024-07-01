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

(* Remove nested declaration of variables *)
(* Preserves the sequential order defined by a let/in *)
(* declaration such that side effects between them are preserved *)
(* E.g., in [let x = e1 in e2], all side effects in [e1] are done before *)
(* those of [e2] *)
(* [let x = e1 in e2] has the behavior of [let x = e1 before y = e2 in y] *)

(* Invariant: an expression is normalized into a pair [(vardec, eq), e] *)
(* whose meaning is [local vardec do eq in e] *)

open Misc
open Location
open Ident
open Zelus
open Aux
open State
open Mapfold

let empty_eq = eqmake Defnames.empty EQempty

(* a structure to represent nested equations before they are turned into *)
(* Zelus equations *)
type 'a ctx =
  { c_vardec: 'a exp vardec list State.t;
    c_eq: 'a eq State.t }

let empty = { c_vardec = State.Empty; c_eq = State.Empty }

let empty = { c_vardec = State.empty; c_eq = State.empty }
let par { c_vardec = v1; c_eq = c_eq1 } { c_vardec = v2; c_eq = c_eq2 } =
  { c_vardec = State.par v1 v2; c_eq = State.par c_eq1 c_eq2 }
let seq { c_vardec = v1; c_eq = c_eq1 } { c_vardec = v2; c_eq = c_eq2 } =
  { c_vardec = State.seq v1 v2; c_eq = State.seq c_eq1 c_eq2 }
let add_seq eq ({ c_eq } as ctx) =
  { ctx with c_eq = State.seq (State.singleton eq) c_eq }
let add_par eq ({ c_eq } as ctx) =
  { ctx with c_eq = State.par (State.singleton eq) c_eq }
let add_vardec vardec_list ({ c_vardec } as ctx) =
  { ctx with c_vardec = State.Cons(vardec_list, c_vardec) }
				   				      
(* translate a context [ctx] into an environment and an equation *)
let equations eqs =
  (* computes the set of sequential equations *)
  let rec seq eqs eq_list =
    match eqs with
    | State.Empty -> eq_list
    | State.Cons(eq, eqs) -> eq :: seq eqs eq_list
    | State.Seq(eqs1, eqs2) ->
       seq eqs1 (seq eqs2 eq_list)
    | State.Par(eqs1, eqs2) ->
       let par_eq_list = par [] eqs1 in
       let par_eq_list = par par_eq_list eqs2 in
       Aux.par par_eq_list :: eq_list
  (* and the set of parallel equations *)
  and par eq_list eqs =
    match eqs with
    | State.Empty -> eq_list
    | State.Cons(eq, eqs) -> par (eq :: eq_list) eqs
    | State.Seq(eqs1, eqs2) ->
       let seq_eq_list = seq eqs2 [] in
       let seq_eq_list = seq eqs1 seq_eq_list in
       Aux.seq seq_eq_list :: eq_list
    | State.Par(eqs1, eqs2) ->
       par (par eq_list eqs1) eqs2 in
  par [] eqs

(* Translation of expressions *)
let rec expression funs _ e =
  let { e_desc }, acc = Mapfold.expression funs empty e in
  match e_desc with
  | Elet(l, e_let) ->
     let _, ctx_l = funs.leq_t funs empty l in
     let e_let, ctx_e_let = funs.expression funs empty e_let in
     e_let, seq ctx_l ctx_e_let
  | Elocal({ b_vars; b_body }, e) ->
     let _, ctx_body = equation funs empty b_body in
     let e, ctx_e = expression funs empty e in
     e, seq (add_vardec b_vars ctx_body) ctx_e
  | Eop(Eseq, [e1; e2]) ->
     (* [e1; e2] is a short-cut for [let _ = e1 in e2] *)
     let e1, ctx1 = expression funs empty e1 in
     let e2, ctx2 = expression funs empty e2 in
     e2, seq ctx1 (add_seq (Aux.wildpat_eq e1) ctx2)
  | _ -> raise Mapfold.Fallback
				    
(** Translate an equation. *)
and equation funs acc eq =
  let { eq_desc }, acc = Mapfold.equation funs acc eq in
  match eq_desc with 
  | EQand { ordered; eq_list } ->
     let _, ctx = equation_list funs ordered eq_list in
     eqmake Defnames.empty EQempty, ctx
  | EQlocal { b_vars; b_body } ->
     let _, ctx_body = equation funs empty b_body in
     empty_eq, add_vardec b_vars ctx_body
  | _ -> raise Mapfold.Fallback

and equation_list funs ordered eq_list =
  let compose = if ordered then seq else par in
  Util.mapfold
    (fun ctx eq ->
      let _, ctx_eq = equation funs empty eq in
      empty_eq, compose ctx ctx_eq) empty eq_list

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; equation; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
