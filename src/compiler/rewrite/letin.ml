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
(* Preserves the sequential order defined by let/in *)
(* declarations. If side-effects or unsafe functions appear, their *)
(* order given by the let/in is preserved *)
(* E.g., in [let x = e1 in e2], all side effects in [e1] are done before *)
(* those of [e2] *)
(* [let x = e1 in e2] has the behavior of [let x = e1 andthen y = e2 in y] *)

(* Invariant: an expression is normalized into a pair [(vardec, eq), e] *)
(* whose meaning is [local vardec do eq in e] *)
(* An equation is normalized into [local vardec do eq] *)

open Misc
open Location
open Ident
open Zelus
open Aux
open State
open Mapfold

let empty_eq = eqmake Defnames.empty EQempty
let empty_block =
  { b_vars = []; b_body = empty_eq; 
    b_env = Env.empty; b_loc = no_location; b_write = Defnames.empty }

(* a structure to represent nested equations before they are turned into *)
(* Zelus equations *)
type 'a acc =
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
				   				      
(* translate a context [acc] into an environment and an equation *)
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

(* build an equation [local vardec_list do eq done] from [acc] *)
let eq_local { c_vardec; c_eq } =
  let vardec_list = State.fold (@) c_vardec [] in
  let eq = equations c_eq in
  Aux.eq_local (block_make vardec_list eq)     

let e_local { c_vardec; c_eq } e =
  let vardec_list = State.fold (@) c_vardec [] in
  let eq = equations c_eq in
  Aux.e_local (block_make vardec_list eq) e    
  
(* Translation of expressions *)
(* [expression funs { c_vardec; c_eq } e = [e', { c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq in e] and *)
(* [local c_vardec' do c_eq' in e'] are equivalent *)
let rec expression funs acc ({ e_desc } as e) =
  match e_desc with
  | Eop(Eseq, [e1; e2]) ->
     (* [e1; e2] is a short-cut for [let _ = e1 in e2] *)
     let e1, acc = expression funs acc e1 in
     let e2, acc = expression funs acc e2 in
     e2, add_seq (Aux.wildpat_eq e1) acc
  | _ -> Mapfold.expression funs acc e

and leq_t funs acc ({ l_eq } as leq) =
  let _, acc = equation funs acc l_eq in
  { leq with l_eq = empty_eq }, add_seq l_eq acc

and block funs acc { b_vars; b_body } =
  let _, acc = equation funs acc b_body in
  empty_block, add_vardec b_vars (add_seq b_body acc)

and match_handler_eq funs acc ({ m_body } as m_h) =
  let _, acc_local = equation funs empty m_body in 
  { m_h with m_body = eq_local acc_local }, acc

and match_handler_e funs acc ({ m_body } as m_h) =
  let e, acc_local = expression funs empty m_body in 
  { m_h with m_body = e_local acc_local e }, acc

and result funs acc ({ r_desc } as r) =
  let r_desc, acc = match r_desc with
  | Exp(e) ->
     let e, acc_local = expression funs empty e in
     Exp(e_local acc_local e), acc
  | Returns({ b_vars; b_body } as b) ->
     let _, acc_local = equation funs empty b_body in
     Returns({ b with b_vars; b_body = eq_local acc_local }), acc in
  { r with r_desc }, acc

(* Translate an equation. *)
(* [equation funs { c_vardec; c_eq } eq = [eq', { c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq and eq] and *)
(* [local c_vardec' do c_eq' and eq'] are equivalent *)
and equation funs acc ({ eq_desc } as eq) =
  match eq_desc with 
  | EQand { ordered; eq_list } ->
     let compose = if ordered then seq else par in
     let acc = List.fold_left
       (fun acc eq ->
         let _, acc_eq = Mapfold.equation funs empty eq in
         compose acc acc_eq) acc eq_list in
     empty_eq, acc
  | _ -> Mapfold.equation funs acc eq

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; leq_t; block; match_handler_eq;
                            match_handler_e; result; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
