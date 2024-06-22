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

(* generic mapfold iterator on the Zelus AST *)
(* it is based on a technique used in the Heptagon compiler in 2012 *)
(* The text below is borrowed from the Heptagon compiler *)
(* https://gitlab.inria.fr/synchrone/heptagon *)

(* The basic idea is to provide a top-down pass over an Heptagon AST. If you
   call [program_it hept_funs_default acc p], with [p] an heptagon program and
   [acc] the accumulator of your choice, it will go through the whole AST,
   passing the accumulator without touching it, and applying the identity
   function on the AST. It'll return [p, acc].

   To customize your pass, you need to redefine some functions of the
   [hept_funs_default] record. Each field in the record handles one node type,
   and the function held in the field will be called when the iterator
   encounters the corresponding node type.

   You can imitate the default functions defined here, and named corresponding
   to the [hep_it_funs] field (corresponding to the Zelus AST type).  There
   are two types of functions, the ones handling record types, and the more
   special ones handling sum types. If you don't want to deal with every
   constructor, you can simply finish your matching with [| _ -> raise
   Misc.Fallback]: it will then fall back to the generic handling for these
   construtors, defined in this file.

   Note that the iterator is a top-down one. If you want to use it in a
   bottom-up manner (e.g. visiting expressions before visiting an equation), you
   need to manually call the proper recursive function (defined here) in the
   beginning of your handler. For example:

   [
   let eq funs acc eq =
     let (eq, acc) = Mapfold.eq funs acc eq in
     ...
     (eq, acc)
   ]

   The record provided here and the functions to iterate over any type
   ([type_it]) enable lots of different ways to deal with the AST.

   Discover it by yourself !*)

(* /!\ Do not EVER put in your funs record one of the generic iterator function
   [type_it]. You should always put a custom version or the default version
   provided in this file. Trespassers will loop infinitely! /!\ *)

open Misc
open Error
open Ast
open Defnames

(* preliminary version *)

exception Fallback

let stop funs _ _ = raise Fallback

type ('a, 'info) global_it_funs =
  {
    var_ident : ('a, 'info) global_it_funs -> 'a -> Ident.t -> Ident.t * 'a;
  }

type ('a, 'info) it_funs =
  {
    global_funs : ('a, 'info) global_it_funs;
    pattern : ('a, 'info) it_funs -> 'a -> 'info pattern -> 'info pattern * 'a;
    type_expression :
      ('a, 'info) it_funs -> 'a -> type_expression -> type_expression * 'a;
    write_t :
      ('a, 'info) it_funs -> 'a -> defnames -> defnames * 'a;
    leq_t :
      ('a, 'info) it_funs -> 'a -> 'info leq -> 'info leq * 'a;
    equation :
      ('a, 'info) it_funs -> 'a -> 'info eq -> 'info eq * 'a;
    scondpat :
      ('a, 'info) it_funs -> 'a -> 'info scondpat -> 'info scondpat * 'a;
    expression :
      ('a, 'info) it_funs -> 'a -> 'info exp -> 'info exp * 'a;
    vardec :
      ('a, 'info) it_funs -> 'a -> 'info exp vardec -> 'info exp vardec * 'a;
    block :
      ('a, 'info) it_funs -> 'a ->
      ('info, 'info exp, 'info eq) block ->
      ('info, 'info exp, 'info eq) block * 'a;
    result :
      ('a, 'info) it_funs -> 'a -> 'info result -> 'info result * 'a;
  }

let rec pattern_it funs acc p =
  try funs.pattern funs acc p
  with Fallback -> pattern funs acc p

and pattern funs acc ({ pat_desc } as p) =
  let pat_desc, acc = match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> pat_desc, acc
    | Evarpat(v) ->
       let v, acc = var_ident_it funs.global_funs acc v in
       Evarpat(v), acc
    | Etuplepat(p_list) ->
       let p_list, acc = Util.mapfold (pattern_it funs) acc p_list in
       Etuplepat(p_list), acc
    | Econstr1pat(c, p_list) ->
       let p_list, acc = Util.mapfold (pattern_it funs) acc p_list in
       Econstr1pat(c, p_list), acc
    | Erecordpat(n_p_list) ->
       let n_p_list, acc =
         Util.mapfold 
           (fun acc { label; arg } ->
             let p, acc = pattern_it funs acc p in
             { label; arg = p}, acc) acc n_p_list in
       Erecordpat(n_p_list), acc
    | Ealiaspat(p1, n) ->
       let p1, acc = pattern_it funs acc p1 in
       let n, acc = var_ident_it funs.global_funs acc n in
       Ealiaspat(p1, n), acc
    | Eorpat(p1, p2) ->
       let p1, acc = pattern_it funs acc p1 in
       let p2, acc = pattern_it funs acc p2 in
       Eorpat(p1, p2), acc
    | Etypeconstraintpat(p1, ty) ->
       let p1, acc = pattern_it funs acc p1 in
       let ty, acc = type_expression_it funs acc ty in
       Etypeconstraintpat(p1, ty), acc in
  { p with pat_desc }, acc

and var_ident_it funs acc x =
  funs.var_ident funs acc x

and var_ident funs acc x = x, acc

and type_expression_it funs acc ty =
  try funs.type_expression funs acc ty
  with Fallback -> type_expression funs acc ty

and type_expression funs acc ty = ty, acc

let rec write_it funs acc { dv; di; der } =
  let rename n = let m, _ = var_ident_it funs acc n in m in
  let dv = Ident.S.map rename dv in
  let di = Ident.S.map rename di in
  let der = Ident.S.map rename der in
  { dv; di; der }, acc

and write_t funs acc w =
  try funs.write_t funs acc w with Fallback -> write_t funs acc w

let default_t f acc d =
  match d with
  | Init(e) -> let e, acc = f acc e in Init(e), acc
  | Else(e) -> let e, acc = f acc e in Else(e), acc
  | NoDefault -> NoDefault, acc

let for_exit_t expression acc ({ for_exit } as fe) =
  let for_exit, acc = expression acc for_exit in
  { fe with for_exit }, acc

let for_kind_t expression acc for_kind =
  match for_kind with
  | Kforeach -> Kforeach, acc
  | Kforward(for_exit_opt) ->
     let for_exit_opt, acc = 
       Util.optional_with_map (for_exit_t expression) acc for_exit_opt in
     Kforward(for_exit_opt), acc
    
let for_size_t expression acc e = expression acc e

let for_input_t var_ident expression acc ({ desc } as fi) =
  let desc, acc = match desc with
    | Einput {id; e; by } ->
       let id, acc = var_ident acc id in
       let e, acc = expression acc e in
       let by, acc = Util.optional_with_map expression acc by in
       Einput { id; e; by }, acc
    | Eindex ({ id; e_left; e_right } as ind) ->
       let id, acc = var_ident acc id in
       let e_left, acc = expression acc e_left in
       let e_right, acc = expression acc e_right in
       Eindex { ind with id; e_left; e_right }, acc in
  { fi with desc }, acc

let slet_it funs acc leq_list =
  Util.mapfold (funs.leq_t funs) acc leq_list

let rec leq_it funs acc leq =
  try funs.leq_t funs acc leq
  with Fallback -> leq_t funs acc leq

and leq_t funs acc ({ l_eq } as leq) =
  let l_eq, acc = funs.equation funs acc l_eq in
  { leq with l_eq }, acc

and scondpat_it funs acc scpat =
  try funs.scondpat funs acc scpat
  with Fallback -> scondpat funs acc scpat

and scondpat funs acc ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     let scpat1, acc = funs.scondpat funs acc scpat1 in
     let scpat2, acc = funs.scondpat funs acc scpat2 in
     { scpat with desc = Econdand(scpat1, scpat2) }, acc
  | Econdor(scpat1, scpat2) ->
     let scpat1, acc = funs.scondpat funs acc scpat1 in
     let scpat2, acc = funs.scondpat funs acc scpat2 in
     { scpat with desc = Econdor(scpat1, scpat2) }, acc
  | Econdexp(e) ->
     let e, acc = funs.expression funs acc e in
     { scpat with desc = Econdexp(e) }, acc
  | Econdpat(e, p) ->
     let e, acc = funs.expression funs acc e in
     let p, acc = funs.pattern funs acc p in
     { scpat with desc = Econdpat(e, p) }, acc
  | Econdon(scpat, e) ->
     let scpat, acc = funs.scondpat funs acc scpat in
     let e, acc = funs.expression funs acc e in
     { scpat with desc = Econdon(scpat, e) }, acc

let rec vardec_it funs acc v =
  try funs.vardec funs acc v
  with Fallback -> vardec funs acc v

and vardec funs acc ({ var_default; var_init; var_typeconstraint } as v) =
  let var_default, acc =
    Util.optional_with_map (funs.expression funs) acc var_default in
  let var_init, acc =
    Util.optional_with_map (funs.expression funs) acc var_init in
  let var_typeconstraint, acc =
    Util.optional_with_map (funs.type_expression funs) acc var_typeconstraint in
  { v with var_default; var_init; var_typeconstraint }, acc

let rec block_it funs acc b =
  try funs.block funs acc b
  with Fallback -> block funs acc b

and block funs acc ({ b_vars; b_body; b_write } as b) =
  let b_vars, acc = 
    Util.mapfold (funs.vardec funs) acc b_vars in
  let b_body, acc = funs.equation funs acc b_body in
  let b_write, acc = funs.write_t funs acc b_write in
  { b with b_vars; b_body; b_write }, acc

let rec result_it funs acc r =
  try funs.result funs acc r
  with Fallback -> result funs acc r

and result funs acc ({ r_desc } as r) =
  let r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc = funs.expression funs acc e in Exp(e), acc
    | Returns(b_eq) ->
       let b_eq, acc = funs.block funs acc b_eq in Returns(b_eq), acc in
  { r with r_desc }, acc

let equation funs acc eq = eq, acc

let expression funs acc e = e, acc

let defaults =
  { global_funs = { var_ident };
    pattern;
    type_expression;
    write_t;
    leq_t;
    equation;
    scondpat;
    expression;
    vardec;
    block;
    result;}
                 
let defaults_stop =
  { global_funs = { var_ident = stop };
    pattern = stop;
    type_expression = stop;
    write_t = stop;
    leq_t = stop;
    equation = stop;
    scondpat = stop;
    expression = stop;
    vardec = stop;
    block = stop;
    result = stop }

