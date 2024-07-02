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

(* add an equation [lx = last* x] for every variable declared in block *)
(* of equations and replace [last x] by lx *)
(* this step is necessary to make static scheduling possible. It may *)
(* introduce useless copies. *)

open Location
open Zelus
open Ident
open Aux

type acc = { renaming : Ident.t Env.t; (* associate names to names *) }

(* Make an equation [lx = last x] *)
let eq_last lx x = Aux.id_eq lx (Aux.last_star x)

(* replace occurrences of [last x] by [lx] *)
let expression funs acc e =
  let { e_desc }, acc = Mapfold.expression funs acc e in
  let e_desc = match e_desc with
    | Elast { copy; id } ->
       if copy then
         try Evar(Env.find id acc.renaming) with Not_found -> e_desc
       else e_desc
    | Eleq(l, e) ->
    | Elocal(b, e) ->
    | _ -> raise Mapfold.Fallback in
  { e with e_desc = e_desc }
    
(** Translation of equations. *)
and equation funs acc eq =
  let { eq_desc }, acc = Mapfold.equation funs acc eq in
  match eq_desc with
  | EQlocal(b) -> 
  | EQlet(l, eq) ->
  | _ -> raise Mapfold.Fallback  
									  
and equation_list subst eq_list = List.map (equation subst) eq_list
						 
(* Translate a generic block *)
and block_eq_list_with_substitution subst
				    ({ b_vars = vardec_list;
				       b_locals = l_list; b_body = eq_list;
				       b_env = b_env } as b) =
  (* Identify variables [last x] in [b_env] *)
  let b_env_last_list, subst, eq_last_list = env subst b_env in
  let l_list, subst = locals subst l_list in
  (* translate the body. *)
  let eq_list = equation_list subst eq_list in
  subst,
  extend_block { b with b_locals = l_list; b_body = eq_list }
    b_env_last_list eq_last_list

and local subst ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_env_last_list, subst, eq_last_list = env subst l_env in
  let l_eq_list = equation_list subst l_eq_list in
  { l with l_eq = eq_last_list @ l_eq_list;
	   l_env = Env.append l_env_last_list l_env }, subst

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; equation;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs () p in
  { p with p_impl_list = p_impl_list }
