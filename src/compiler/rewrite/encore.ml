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

(* An horizon [local horizon h default infinity] with and equation *)
(* [h = 0.0] is added in every branch activated on a zero-crossing *)
(* which writes a non local state variable *)
(* match e with | P1 -> (* zero *) x = ... | Pn -> ... *)
(* into:  match e with | P1 -> do h = 0.0 and x = ... | ... *)

open Ident
open Initial
open Zelus
open Aux
open Defnames
open Deftypes
open Mapfold

type acc =
  { env: Deftypes.constant Deftypes.tentry Env.t }

let empty = { env = Env.empty }

(* Does a block contains an equation [x = e] on a last variable? *)
let encore env { dv } =
  let write_on_last x =
    let { t_sort } =
      try Env.find x env
      with Not_found ->
	Format.eprintf "Encore error: unbound name %a\n" Printer.name x;
        raise Misc.Error in
      match t_sort with
      | Sort_mem { m_previous } -> m_previous | _ -> false in
  S.exists write_on_last dv

(* Add an equation [encore = true] *)
let with_zero env encore_opt ({ eq_desc; eq_write } as eq) =
  if encore env eq_write then
    let encore =
      match encore_opt with
	| None -> Ident.fresh "encore" | Some(encore) -> encore in
    let { eq_write } as eq = Aux.eq_and (Aux.id_eq encore Aux.zero) eq in
    { eq with eq_write = { eq_write with dv = S.add encore eq_write.dv } },
    Some(encore)
  else eq, encore_opt
    
(* Translation of equations *)
let equation funs acc eq =
  let { eq_desc }, ({ env } as acc) = funs.equation funs acc eq in
  match eq_desc with 
  | EQmatch({ handlers } as m) ->
     (* add an equation [h = 0.0] if at least one branch is activated *)
     (* on a zero-crossing and changes a non local state variable *)
     (* whose last value is read *)
     let handlers, encore =
       Util.mapfold
	 (fun encore_opt ({ m_zero; m_body } as m_h) ->
	   let m_body, encore_opt =
	     if m_zero then with_zero env encore_opt m_body
	     else m_body, encore_opt in
	   { m_h with m_body }, encore_opt)
	 None handlers in
     let eq = { eq with eq_desc = EQmatch { m with handlers } } in
     begin match encore with
     | None -> eq, acc
     | Some(encore) ->
        Aux.eq_local
          (Aux.block_make [Aux.vardec encore false None (Some(Aux.infinity))]
             [eq]), acc
     end
    | _ -> raise Mapfold.Fallback

let build funs { env } b_env =
  b_env, { env = Env.append b_env env }

  
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = { Mapfold.default_global_funs with build } in
  let funs =
    { Mapfold.defaults with equation; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
