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
(* [expression funs { c_vardec; c_eq } e = [e', { c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq in e] and [local c_vardec' do c_eq' in e'] *)
(* are equivalent *)
let expression funs acc e =
  let { e_desc }, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Elet(l, e_let) ->
     let l, acc = Mapfold.leq_t funs acc l in
     let e_let, acc = Mapfold.expression funs acc e_let in
     e_let, acc
  | Elocal({ b_vars; b_body }, e) ->
     let _, acc = Mapfold.equation funs acc b_body in
     let e, acc = Mapfold.expression funs acc e in
     e, add_vardec b_vars acc
  | Eop(Eseq, [e1; e2]) ->
     (* [e1; e2] is a short-cut for [let _ = e1 in e2] *)
     let e1, acc = Mapfold.expression funs acc e1 in
     let e2, acc = Mapfold.expression funs acc e2 in
     e2, add_seq (Aux.wildpat_eq e1) acc
  | _ -> e, acc

and leq_t funs acc ({ l_eq } as leq) =
  let l_eq, acc = Mapfold.equation funs acc l_eq in
  { leq with l_eq = empty_eq }, add_seq l_eq acc

(*
  let funexp funs acc f =
  let { f_args; f_body; f_env } as f, acc = Mapfold.funexp funs acc f in
  { f with f_body = doin acc f_body }, empty
 *)

(* Translate an equation. *)
(* [equation funs { c_vardec; c_eq } eq = [eq', { c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq and eq] and [local c_vardec' do c_eq' and e']*)
(* are equivalent *)
let rec equation funs acc eq =
  let ({ eq_desc } as eq), acc = Mapfold.equation funs acc eq in
  match eq_desc with 
  | EQand { ordered; eq_list } ->
     let _, acc = equation_list funs ordered acc eq_list in
     eqmake Defnames.empty EQempty, acc
  | EQlocal { b_vars; b_body } ->
     let _, acc = Mapfold.equation funs acc b_body in
     empty_eq, add_vardec b_vars acc
  | EQlet(leq, eq) ->
     let _, acc = Mapfold.leq_t funs acc leq in
     let b, acc = Mapfold.equation funs acc eq in
     empty_eq, acc
  | _ -> empty_eq, add_seq eq acc

and equation_list funs ordered acc eq_list =
  let compose = if ordered then seq else par in
  Util.mapfold
    (fun acc eq ->
      let _, acc_eq = Mapfold.equation funs empty eq in
      empty_eq, compose acc acc_eq) acc eq_list

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; equation; leq_t; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
