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

(* removing equations [der x = e init e0 reset z1 -> e1 | ... | zn -> en] *)

open Misc
open Location
open Ident
open Zelus
open Aux

(* An equation: [der x = e1 init e0 reset z1 -> e1 | ... | zn -> en] *)
(* into: [init x = e0 *)
(*        and present (z1) -> do x = e1 done | ... end and der x = e] *)

let block_of_eq s pat e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQeq(pat, e))]; 
    b_loc = no_location; b_write = { Deftypes.empty with dv = s };
    b_env = Env.empty }

let block_of_der s x e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQder(x, e, None, []))]; 
    b_loc = no_location; 
    b_write = { Deftypes.empty with der = s }; b_env = Env.empty }
    
let block_spat_e_list s pat spat_e_list =
  List.map 
    (fun { p_cond = spat; p_body = e; p_env = env; p_zero = zero } ->
      { p_cond = spat;
        p_body = block_of_eq s pat e;
        p_env = env; p_zero = zero }) spat_e_list

let present s x spat_e_list e eq_list =
  let spat_b_list =
    block_spat_e_list s (varpat x Initial.typ_float) spat_e_list in
  (* only generate a present if [spat_b_list] is not empty *)
  match spat_b_list with
    | [] -> (eq_der x e) :: eq_list
    | _ -> (eqmake (EQpresent(spat_b_list, None))) :: (eq_der x e) :: eq_list

let der_present x e e0_opt spat_e_list eq_list =
  (* present z1 -> do x = e1 done | ... | zn -> do x = en done
     else der x = e and init x = e0 *)
  let eq_list = 
    match e0_opt with
    | None -> eq_list
    | Some(e0) -> (eq_init x e0) :: eq_list in
  present (S.singleton x) x spat_e_list e eq_list  

let equation funs ({ eq_desc = desc } as eq) =
  match desc with
    | EQder(n, e, e0_opt, p_h_e_list) ->
        der_present n e e0_opt p_h_e_list eq_list
    | _ -> raise Mapfold.Fallback

