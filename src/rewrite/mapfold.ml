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
(* this code is adapted from the one of Heptgon. The text below is *)
(* that of the Heptagon compiler: https://gitlab.inria.fr/synchrone/heptagon *)

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

(* preliminary version *)

exception Fallback

let stop funs _ _ = raise Fallback

type ('a, 'info) global_it_funs =
  { var_ident : ('a, 'info) global_it_funs -> 'a -> Ident.t -> Ident.t * 'a;
  }

type ('a, 'info) it_funs = {
    pattern : ('a, 'info) it_funs -> 'a -> 'info pattern -> 'info pattern * 'a;
    global_funs : ('a, 'info) global_it_funs }

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
       Etypeconstraintpat(p1, ty), acc in
  { p with pat_desc }, acc

and var_ident_it funs acc x =
  funs.var_ident funs acc x

and var_ident funs acc x = x, acc

let defaults = {
    pattern;
    global_funs = { var_ident } }
                 
let defaults_stop = {
    pattern = stop;
    global_funs = { var_ident = stop }
  }
                      
