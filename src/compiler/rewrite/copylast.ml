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
let expression funs acc e =
  let { e_desc }, acc = Mapfold.expression funs acc e in
  let e_desc, acc = match e_desc with
    | Elast { copy; id } ->
       if copy then
         try (* if [id] is already in [acc] an associated to [m] *)
           (* replace [last id] by [last*m] *)
           let m = Env.find id acc in
           Elast { copy = false; id = m }, acc
         with Not_found ->
           let m = fresh "m" in
           Elast { copy = false; id = m },
           Env.add id m acc
       else e_desc, acc
    | _ -> raise Mapfold.Fallback in
  { e with e_desc = e_desc }, acc

let leq_t funs acc leq =
  let { l_eq; l_env } as leq, acc = Mapfold.leq_t funs acc leq in
  (* for every entry [x\m] in [l_acc] that appear in [l_env] *)
  (* add an equation [m = x]; update [l_env] and [l_eq.eq_write] *)
  let renaming_list, acc = remove l_env acc in
  { leq with l_eq = Aux.par (l_eq :: List.map eq_copy renaming_list);
             l_env = List.fold_left
                 (fun acc (x, m) -> Env.add m Misc.no_info acc) l_env
                 renaming_list }, acc
  
(* Translation of equations. *)
let equation funs acc eq =
  let { eq_desc }, acc = Mapfold.equation funs acc eq in
  let eq_desc, acc = match eq_desc with
    | EQlocal(b) ->
       let b, acc = block b acc in EQlocal(b), acc
    | EQlet(l, eq) ->
       let l, acc = leq_t l acc in
       let e, acc = Mapfold.expression funs acc e in
       EQlet(l, eq), acc
    | _ -> raise Mapfold.Fallback in
  { eq with eq_desc }, acc
									  
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
