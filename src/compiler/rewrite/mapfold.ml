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
open Zelus
open Defnames

(* preliminary version *)

exception Fallback

let stop funs _ _ = raise Fallback

type ('a, 'info) global_it_funs =
  {
    build :  ('a, 'info) global_it_funs -> 'a ->
            'info Ident.Env.t -> 'info Ident.Env.t * 'a;
    var_ident :
      ('a, 'info) global_it_funs -> 'a -> Ident.t -> Ident.t * 'a;
    typevar :
      ('a, 'info) global_it_funs -> 'a -> name -> name * 'a;
    typeconstr :
      ('a, 'info) global_it_funs -> 'a -> Lident.t -> Lident.t * 'a;
    type_expression :
      ('a, 'info) global_it_funs -> 'a ->
      type_expression -> type_expression * 'a;
    typedecl :
      ('a, 'info) global_it_funs -> 'a ->
      ((name * name list * name list * type_decl) as 'ty) -> 'ty * 'a;
    kind :
      ('a, 'info) global_it_funs -> 'a -> kind -> kind * 'a;
    interface :
      ('a, 'info) global_it_funs -> 'a -> interface -> interface * 'a;
  }

type ('a, 'info) it_funs =
  {
    global_funs : ('a, 'info) global_it_funs;
    pattern : ('a, 'info) it_funs -> 'a -> 'info pattern -> 'info pattern * 'a;
    write_t :
      ('a, 'info) it_funs -> 'a -> defnames -> defnames * 'a;
    leq_t :
      ('a, 'info) it_funs -> 'a -> 'info leq -> 'info leq * 'a;
    equation :
      ('a, 'info) it_funs -> 'a -> 'info eq -> 'info eq * 'a;
    scondpat :
      ('a, 'info) it_funs -> 'a -> 'info scondpat -> 'info scondpat * 'a;
    size_t :
      ('a, 'info) it_funs -> 'a -> size -> size * 'a;
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
    funexp :
      ('a, 'info) it_funs -> 'a -> 'info funexp -> 'info funexp * 'a;
    last :
      ('a, 'info) it_funs -> 'a -> Ident.t -> Ident.t * 'a;
    implementation :
      ('a, 'info) it_funs -> 'a ->
      'info implementation -> 'info implementation * 'a;
    program :
      ('a, 'info) it_funs -> 'a -> 'info program -> 'info program * 'a;
    get_index :
     ('a, 'info) it_funs -> 'a -> Ident.num -> Ident.num * 'a;
    set_index :
      ('a, 'info) it_funs -> 'a -> Ident.num -> Ident.num * 'a;
    open_t :
      ('a, 'info) it_funs -> 'a -> name -> name * 'a;
  }

(** Build a renaming from an environment *)
let rec build_it funs acc env =
  try funs.build funs acc env
  with Fallback -> build funs acc env

and build funs acc env = env, acc

let rec last_it funs acc l =
  try funs.last funs acc l
  with Fallback -> last funs acc l

and last funs acc l =
  funs.global_funs.var_ident funs.global_funs acc l

let rec pattern_it funs acc pat =
  try funs.pattern funs acc pat
  with Fallback -> pattern funs acc pat

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
       let ty, acc = type_expression_it funs.global_funs acc ty in
       Etypeconstraintpat(p1, ty), acc in
  { p with pat_desc }, acc

and var_ident_it global_funs acc x =
  try global_funs.var_ident global_funs acc x
  with Fallback -> var_ident global_funs acc x

and var_ident global_funs acc x = x, acc

and typevar_it global_funs acc x =
  try global_funs.typevar global_funs acc x
  with Fallback -> typevar global_funs acc x

and typevar global_funs acc x = x, acc

and typeconstr_it global_funs acc x =
  try global_funs.typeconstr global_funs acc x
  with Fallback -> typeconstr global_funs acc x

and typeconstr global_funs acc x = x, acc

and kind_it global_funs acc k =
  try global_funs.kind global_funs acc k
  with Fallback -> kind global_funs acc k

and kind global_funs acc k = k, acc

and type_expression_it global_funs acc ty =
  try global_funs.type_expression global_funs acc ty
  with Fallback -> type_expression global_funs acc ty

and type_expression global_funs acc ({ desc } as ty) =
  let desc, acc = match desc with
  | Etypevar(name) ->
     let name, acc = typevar_it global_funs acc name in
     Etypevar(name), acc
  | Etypeconstr(lname, ty_list) ->
     let lname, acc = typeconstr_it global_funs acc lname in
     let ty_list, acc =
       Util.mapfold (type_expression_it global_funs) acc ty_list in
     Etypeconstr(lname, ty_list), acc 
  | Etypetuple(ty_list) ->
     let ty_list, acc =
       Util.mapfold (type_expression_it global_funs) acc ty_list in
     Etypetuple(ty_list), acc     
  | Etypefun(kind, ty1, ty2) ->
     let kind, acc = kind_it global_funs acc kind in
     let ty1, acc = type_expression_it global_funs acc ty1 in
     let ty2, acc = type_expression_it global_funs acc ty2 in
     Etypefun(kind, ty1, ty2), acc in
  { ty with desc }, acc

let rec size_it funs acc si =
  try funs.size_t funs acc si
  with Fallback -> size_t funs acc si

and size_t funs acc ({ desc } as si) =
  let desc, acc = match desc with
  | Sint _ -> desc, acc
  | Sfrac { num; denom } ->
     let num, acc = size_it funs acc num in
     Sfrac { num; denom }, acc
  | Sident(id) ->
     let id, acc = var_ident_it funs.global_funs acc id in
     Sident(id), acc
  | Splus(si1, si2) ->
     let si1, acc = size_it funs acc si1 in
     let si2, acc = size_it funs acc si2 in
     Splus(si1, si2), acc
  | Sminus(si1, si2) ->
     let si1, acc = size_it funs acc si1 in
     let si2, acc = size_it funs acc si2 in
     Splus(si1, si2), acc
  | Smult(si1, si2) ->
     let si1, acc = size_it funs acc si1 in
     let si2, acc = size_it funs acc si2 in
     Splus(si1, si2), acc in
  { si with desc }, acc

let rec write_it funs acc w =
  try funs.write_t funs acc w
  with Fallback -> write_t funs acc w

and write_t funs acc { dv; di; der } =
  let rename n = let m, _ = var_ident_it funs.global_funs acc n in m in
  let dv = Ident.S.map rename dv in
  let di = Ident.S.map rename di in
  let der = Ident.S.map rename der in
  { dv; di; der }, acc

let default_t f acc d =
  match d with
  | Init(e) -> let e, acc = f acc e in Init(e), acc
  | Else(e) -> let e, acc = f acc e in Else(e), acc
  | NoDefault -> NoDefault, acc

let for_exit_t funs acc ({ for_exit } as fe) =
  let for_exit, acc = funs.expression funs acc for_exit in
  { fe with for_exit }, acc

let for_kind_t funs acc for_kind =
  match for_kind with
  | Kforeach -> Kforeach, acc
  | Kforward(for_exit_opt) ->
     let for_exit_opt, acc = 
       Util.optional_with_map (for_exit_t funs) acc for_exit_opt in
     Kforward(for_exit_opt), acc
    
let for_size_t funs acc e = funs.expression funs acc e

let for_input_t funs acc ({ desc } as fi) =
  let desc, acc = match desc with
    | Einput {id; e; by } ->
       let id, acc = funs.global_funs.var_ident funs.global_funs acc id in
       let e, acc = funs.expression funs acc e in
       let by, acc = Util.optional_with_map (funs.expression funs) acc by in
       Einput { id; e; by }, acc
    | Eindex ({ id; e_left; e_right } as ind) ->
       let id, acc = funs.global_funs.var_ident funs.global_funs acc id in
       let e_left, acc = funs.expression funs acc e_left in
       let e_right, acc = funs.expression funs acc e_right in
       Eindex { ind with id; e_left; e_right }, acc in
  { fi with desc }, acc

let rec slet_it funs acc leq_list =
  Util.mapfold (leq_it funs) acc leq_list

and leq_it funs acc leq =
  try funs.leq_t funs acc leq
  with Fallback -> leq_t funs acc leq

and leq_t funs acc ({ l_eq; l_env } as leq) =
  let l_env, acc = build_it funs.global_funs acc l_env in
  let l_eq, acc = equation_it funs acc l_eq in
  { leq with l_eq; l_env }, acc

and scondpat_it funs acc scpat =
  try funs.scondpat funs acc scpat
  with Fallback -> scondpat funs acc scpat

and scondpat funs acc ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     let scpat1, acc = scondpat_it funs acc scpat1 in
     let scpat2, acc = scondpat_it funs acc scpat2 in
     { scpat with desc = Econdand(scpat1, scpat2) }, acc
  | Econdor(scpat1, scpat2) ->
     let scpat1, acc = scondpat_it funs acc scpat1 in
     let scpat2, acc = scondpat_it funs acc scpat2 in
     { scpat with desc = Econdor(scpat1, scpat2) }, acc
  | Econdexp(e) ->
     let e, acc = expression_it funs acc e in
     { scpat with desc = Econdexp(e) }, acc
  | Econdpat(e, p) ->
     let e, acc = expression_it funs acc e in
     let p, acc = pattern_it funs acc p in
     { scpat with desc = Econdpat(e, p) }, acc
  | Econdon(scpat, e) ->
     let scpat, acc = scondpat_it funs acc scpat in
     let e, acc = expression_it funs acc e in
     { scpat with desc = Econdon(scpat, e) }, acc

and vardec_it funs acc v =
  try funs.vardec funs acc v
  with Fallback -> vardec funs acc v

and vardec funs acc
  ({ var_name; var_default; var_init; var_typeconstraint } as v) =
  let var_name, acc =
    var_ident_it funs.global_funs acc var_name in
  let var_default, acc =
    Util.optional_with_map (expression_it funs) acc var_default in
  let var_init, acc =
    Util.optional_with_map (expression_it funs) acc var_init in
  let var_typeconstraint, acc =
    Util.optional_with_map
      (type_expression_it funs.global_funs) acc var_typeconstraint in
  { v with var_name; var_default; var_init; var_typeconstraint }, acc

and block_it funs acc b =
  try funs.block funs acc b
  with Fallback -> block funs acc b

and block funs acc ({ b_vars; b_body; b_write; b_env } as b) =
  let b_env, acc = build_it funs.global_funs acc b_env in
  let b_vars, acc = 
    Util.mapfold (vardec_it funs) acc b_vars in
  let b_body, acc = equation_it funs acc b_body in
  let b_write, acc = write_t funs acc b_write in
  { b with b_vars; b_body; b_env; b_write }, acc

and result_it funs acc r =
  try funs.result funs acc r
  with Fallback -> result funs acc r

and result funs acc ({ r_desc } as r) =
  let r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc = expression_it funs acc e in Exp(e), acc
    | Returns(b_eq) ->
       let b_eq, acc = block_it funs acc b_eq in Returns(b_eq), acc in
  { r with r_desc }, acc

and funexp_it funs acc f =
  try funs.funexp funs acc f
  with Fallback -> funexp funs acc f

and funexp funs acc ({ f_args; f_body; f_env } as f) =
  let arg acc v_list = Util.mapfold (vardec_it funs) acc v_list in
  let f_env, acc = build_it funs.global_funs acc f_env in
  let f_args, acc = Util.mapfold arg acc f_args in
  let f_body, acc = result_it funs acc f_body in
  { f with f_args; f_body; f_env }, acc

(** Expressions **)
and expression_it funs acc e =
  try funs.expression funs acc e
  with Fallback -> expression funs acc e

and expression funs acc ({ e_desc; e_loc } as e) =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e, acc
  | Evar(x) ->
     let x, acc = var_ident_it funs.global_funs acc x in
     { e with e_desc = Evar(x) }, acc
  | Elast(x) ->
     let x, acc = last_it funs acc x in
     { e with e_desc = Elast(x) }, acc
  | Etuple(e_list) ->
     let e_list, acc = Util.mapfold (expression_it funs) acc e_list in
     { e with e_desc = Etuple(e_list) }, acc
  | Econstr1 { lname; arg_list } ->
     let arg_list, acc = Util.mapfold (expression_it funs) acc arg_list in
     { e with e_desc = Econstr1 { lname; arg_list } }, acc
  | Erecord(l_e_list) -> 
      let l_e_list, acc =
        Util.mapfold (fun acc { label; arg } ->
            let arg, acc = expression_it funs acc arg in 
            { label; arg }, acc) acc l_e_list in
      { e with e_desc = Erecord(l_e_list) }, acc
  | Erecord_access { label; arg } ->
      let arg, acc = expression_it funs acc arg in
      { e with e_desc = Erecord_access { label; arg } }, acc
  | Erecord_with(e_record, l_e_list) -> 
     let e_record, acc = expression_it funs acc e_record in
     let l_e_list, acc =
       Util.mapfold
	  (fun acc { label; arg } ->
            let arg, acc = expression_it funs acc e in { label; arg }, acc)
          acc l_e_list in
      { e with e_desc = Erecord_with(e_record, l_e_list) }, acc
  | Eapp ({ f; arg_list } as a) ->
     let arg_list, acc = Util.mapfold (expression_it funs) acc arg_list in
     let f, acc = expression_it funs acc f in
     { e with e_desc = Eapp { a with f; arg_list } }, acc
  | Eop(op, e_list) ->
     let e_list, acc = Util.mapfold (expression_it funs) acc e_list in
     { e with e_desc = Eop(op, e_list) }, acc
  | Etypeconstraint(e_ty, ty) ->
     let e_ty, acc = expression_it funs acc e_ty in
     let ty, acc = type_expression_it funs.global_funs acc ty in
     { e with e_desc = Etypeconstraint(e_ty, ty) }, acc
  | Elet(l, e_let) ->
     let l, acc = leq_it funs acc l in
     let e_let, acc = expression_it funs acc e_let in
     { e with e_desc = Elet(l, e_let) }, acc
  | Elocal(eq_b, e) ->
     let eq_b, acc = block_it funs acc eq_b in
     let e, acc = expression_it funs acc e in
     { e with e_desc = Elocal(eq_b, e) }, acc
  | Epresent({ handlers; default_opt }) ->
     let body acc ({ p_cond; p_body; p_env } as p_b) =
       let p_env, acc = build_it funs.global_funs acc p_env in
       let p_cond, acc = scondpat_it funs acc p_cond in
       let p_body, acc = expression_it funs acc p_body in
       { p_b with p_cond; p_body }, acc in
     let handlers, acc =
       Util.mapfold body acc handlers in
     let default_opt, acc = default_t (expression_it funs) acc default_opt in
     { e with e_desc = Epresent { handlers; default_opt } }, acc 
  | Ematch({ e; handlers } as m) ->
     let body acc ({ m_pat; m_body; m_env } as m_h) =
       let m_env, acc = build_it funs.global_funs acc m_env in
       let m_pat, acc = pattern_it funs acc m_pat in
       let m_body, acc = expression_it funs acc m_body in
       { m_h with m_pat; m_body; m_env }, acc in
     let e, acc = expression_it funs acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
     { e with e_desc = Ematch { m with e; handlers } }, acc
  | Eassert e -> let e, acc = expression_it funs acc e in
                 { e with e_desc = Eassert(e) }, acc
  | Ereset(e_body, e_c) ->
     let e_body, acc = expression_it funs acc e_body in
     let e_c, acc = expression_it funs acc e_c in
     { e with e_desc = Ereset(e_body, e_c) }, acc
  | Esizeapp { f; size_list } -> 
     let size_list, acc = Util.mapfold (size_it funs) acc size_list in
     let v, acc = expression_it funs acc f in
     { e with e_desc = Esizeapp { f; size_list } }, acc
  | Efun f ->
     let f, acc = funexp_it funs acc f in
     { e with e_desc = Efun f }, acc
  | Eforloop
     ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
     let for_vardec_t acc ({ desc = { for_array; for_vardec } } as f) =
       let for_vardec, acc = vardec_it funs acc for_vardec in
       { f with desc = { for_array; for_vardec } }, acc in
     let for_exp_t acc for_exp =
       match for_exp with
       | Forexp { exp; default } ->
          let exp, acc = expression_it funs acc exp in
          let default, acc =
            Util.optional_with_map (expression_it funs) acc default in
          Forexp { exp; default }, acc
       | Forreturns { returns; body; r_env } ->
          let r_env, acc = build_it funs.global_funs acc r_env in
          let returns, acc = Util.mapfold for_vardec_t acc returns in
          let body, acc = block_it funs acc body in
          Forreturns { returns; body; r_env }, acc in
     let for_env, acc = build_it funs.global_funs acc for_env in
     let for_index, acc =
       Util.optional_with_map (var_ident_it funs.global_funs) acc for_index in
     let for_size, acc =
       Util.optional_with_map (for_size_t funs) acc for_size in
     let for_kind, acc = for_kind_t funs acc for_kind in
     let for_input, acc =
       Util.mapfold (for_input_t funs) acc for_input in
     let for_body, acc = for_exp_t acc for_body in
     { e with e_desc =
                Eforloop
                  { f with for_size; for_kind; for_index; for_input;
                           for_body; for_env } }, acc

(** Equations **)
and equation_it funs acc eq =
  try funs.equation funs acc eq
  with Fallback -> equation funs acc eq

and equation funs acc ({ eq_desc; eq_write; eq_loc } as eq) = 
  let eq_write, acc = write_t funs acc eq_write in
  let eq, acc = match eq_desc with
    | EQeq(p, e) ->
       let p, acc = pattern_it funs acc p in
       let e, acc = expression_it funs acc e in
       { eq with eq_desc = EQeq(p, e) }, acc
    | EQinit(x, e) ->
       let x, acc = var_ident_it funs.global_funs acc x in
       let e, acc = expression_it funs acc e in
       { eq with eq_desc = EQinit(x, e) }, acc
    | EQemit(x, e_opt) ->
       let x, acc = var_ident_it funs.global_funs acc x in
       let e_opt, acc =
         Util.optional_with_map (expression_it funs) acc e_opt in
       { eq with eq_desc = EQemit(x, e_opt) }, acc
    | EQder { id; e; e_opt; handlers } ->
       let body acc ({ p_cond; p_body; p_env } as p_b) =
         let p_env, acc = build_it funs.global_funs acc p_env in
         let p_cond, acc = scondpat_it funs acc p_cond in
         let p_body, acc = expression_it funs acc p_body in
         { p_b with p_cond; p_body }, acc in
       let id, acc = var_ident_it funs.global_funs acc id in
       let e, acc = expression_it funs acc e in
       let e_opt, acc =
         Util.optional_with_map (funs.expression funs) acc e_opt in
       let handlers, acc = Util.mapfold body acc handlers in
       { eq with eq_desc = EQder { id; e; e_opt; handlers } }, acc
    | EQif { e; eq_true; eq_false } ->
       let e, ac = expression_it funs acc e in
       let eq_true, acc = equation_it funs acc eq_true in
       let eq_false, acc = equation_it funs acc eq_false in
       { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
    | EQmatch({ e; handlers } as m) ->
       let body acc ({ m_pat; m_body; m_env } as m_h) =
         let m_env, acc = build_it funs.global_funs acc m_env in
         let m_pat, acc = pattern_it funs acc m_pat in
         let m_body, acc = equation_it funs acc m_body in
         { m_h with m_pat; m_body; m_env }, acc in
       let e, acc = expression_it funs acc e in
       let handlers, acc =
         Util.mapfold body acc handlers in
       { eq with eq_desc = EQmatch { m with e; handlers } }, acc
    | EQlocal(eq_b) ->
       let eq_b, acc = block_it funs acc eq_b in
       { eq with eq_desc = EQlocal(eq_b) }, acc
    | EQand(eq_list) ->
       let eq_list, acc = Util.mapfold (equation_it funs) acc eq_list in
       { eq with eq_desc = EQand(eq_list) }, acc
    | EQpresent({ handlers; default_opt }) ->
       let body acc ({ p_cond; p_body; p_env } as p_b) =
         let p_env, acc = build_it funs.global_funs acc p_env in
         let p_cond, acc = scondpat_it funs acc p_cond in
         let p_body, acc = equation_it funs acc p_body in
         { p_b with p_cond; p_body }, acc in
       let handlers, acc = Util.mapfold body acc handlers in
       let default_opt, acc = default_t (equation_it funs) acc default_opt in
       { eq with eq_desc = EQpresent { handlers; default_opt } }, acc
    | EQautomaton({ handlers; state_opt } as a) ->
       let statepat acc ({ desc } as spat) =
         let desc, acc = match desc with
           | Estate0pat(id) ->
              let id, acc = var_ident_it funs.global_funs acc id in
            Estate0pat(id), acc
         | Estate1pat(id, id_list) ->
            let id, ac = var_ident_it funs.global_funs acc id in
            let id_list, acc =
              Util.mapfold (var_ident_it funs.global_funs)
                acc id_list in
            Estate1pat(id, id_list), acc in
         { spat with desc }, acc in
       let rec state acc ({ desc } as st) =
         let desc, acc  = match desc with
           | Estate0(id) ->
              let id, acc = var_ident_it funs.global_funs acc id in
              Estate0(id), acc
           | Estate1(id, e_list) ->
              let id, acc =  var_ident_it funs.global_funs acc id in
              let e_list, acc =
                Util.mapfold (expression_it funs) acc e_list in
              Estate1(id, e_list), acc
           | Estateif(e, st1, st2) ->
              let e, acc = expression_it funs acc e in
              let st1, acc = state acc st1 in
              let st2, acc = state acc st2 in
              Estateif(e, st1, st2), acc in
         { st with desc }, acc in
       let escape acc ({ e_cond; e_let; e_body; e_next_state; e_env } as esc) =
         let e_env, acc = build_it funs.global_funs acc e_env in
         let e_cond, acc = scondpat_it funs acc e_cond in
         let e_let, acc = slet_it funs acc e_let in
         let e_body, acc = block_it funs acc e_body in
         let e_next_state, acc = state acc e_next_state in
         { esc with e_cond; e_let; e_body; e_next_state; e_env }, acc in
       let handler acc ({ s_state; s_let; s_body; s_trans } as h) =
         let s_state, acc = statepat acc s_state in
         let s_let, acc = slet_it funs acc s_let in
         let s_body, acc = block_it funs acc s_body in
         let s_trans, acc = Util.mapfold escape acc s_trans in
         { h with s_state; s_let; s_body; s_trans }, acc in
       let state_opt, acc = Util.optional_with_map state acc state_opt in
       let handlers, acc = Util.mapfold handler acc handlers in
       { eq with eq_desc = EQautomaton({ a with handlers; state_opt }) }, acc
    | EQempty -> eq, acc
    | EQassert(e) ->
       let e, acc = expression_it funs acc e in
       { eq with eq_desc = EQassert(e) }, acc
    | EQforloop
       ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
       let for_eq_t acc { for_out; for_block } =
         let for_out_t acc
               ({ desc = { for_name; for_out_name; for_init; for_default } }
                as f) =
           let for_name, acc = var_ident_it funs.global_funs acc for_name in
           let for_out_name, acc = 
             Util.optional_with_map
               (var_ident_it funs.global_funs) acc for_out_name in
           let for_init, acc =
             Util.optional_with_map (expression_it funs) acc for_init in
           let for_default, acc =
             Util.optional_with_map (expression_it funs) acc for_default in
           { f with desc = { for_name; for_out_name; for_init; for_default } },
           acc in
         let for_out, acc =
           Util.mapfold for_out_t acc for_out in
         let for_block, acc = block_it funs acc for_block in
         { for_out; for_block }, acc in
       let for_env, acc = build_it funs.global_funs acc for_env in
       let for_size, acc =
         Util.optional_with_map (for_size_t funs) acc for_size in
       let for_kind, acc = for_kind_t funs acc for_kind in
       let for_input, acc =
         Util.mapfold (for_input_t funs) acc for_input in
       let for_body, acc = for_eq_t acc for_body in
       { eq with eq_desc =
                   EQforloop
                     { f with for_size; for_kind; for_index; for_input;
                              for_body; for_env } }, acc
    | EQreset(eq, e_c) ->
       let eq, acc = equation_it funs acc eq in
       let e_c, acc = expression_it funs acc e_c in
       { eq with eq_desc = EQreset(eq, e_c) }, acc
    | EQlet(leq, eq) ->
       let leq, acc = leq_it funs acc leq in
       let eq, acc = equation_it funs acc eq in
       { eq with eq_desc = EQlet(leq, eq) }, acc
    | EQsizefun({ sf_id; sf_id_list; sf_e; sf_env } as sf) ->
       let sf_env, acc = build_it funs.global_funs acc sf_env in
       let sf_id, acc = var_ident_it funs.global_funs acc sf_id in
       let sf_id_list, acc =
         Util.mapfold (var_ident_it funs.global_funs) acc sf_id_list in
       let sf_e, acc = expression_it funs acc sf_e in
       { eq with eq_desc =
                   EQsizefun { sf with sf_id; sf_id_list; sf_e; sf_env } },
       acc in
  { eq with eq_write }, acc

let rec typedecl_it funs acc ty_decl =
  try funs.typedecl funs acc ty_decl
  with Fallback -> typedecl funs acc ty_decl

and typedecl funs acc ty_decl = ty_decl, acc

let open_it funs acc name = funs.open_t funs acc name

let open_t funs acc name = name, acc

let rec implementation_it funs acc impl =
  try funs.implementation funs acc impl
  with Fallback -> implementation funs acc impl

and implementation funs acc ({ desc } as impl) =
  let desc, acc = match desc with
    | Eopen(name) ->
       let name, acc = open_it funs acc name in
       Eopen(name), acc
    | Eletdecl { d_names; d_leq } ->
       let d_leq, acc = leq_it funs acc d_leq in
       let d_names, acc =
         Util.mapfold
           (fun acc (name, id) ->
             let id, acc =
               var_ident_it funs.global_funs acc id in (name, id), acc)
           acc d_names in
       Eletdecl { d_names; d_leq }, acc
    | Etypedecl { name; ty_params; size_params; ty_decl } ->
       let (name, ty_params, size_params, ty_decl), acc =
         typedecl_it
           funs.global_funs acc (name, ty_params, size_params, ty_decl) in
       Etypedecl { name; ty_params; size_params; ty_decl }, acc in
  { impl with desc }, acc

let rec set_index_it funs acc n =
  try funs.set_index funs acc n 
  with Fallback -> set_index funs acc n

and set_index funs acc n = n, acc

let rec get_index_it funs acc n =
  try funs.get_index funs acc n
  with Fallback -> get_index funs acc n

and get_index funs acc n = n, acc

let rec program_it funs acc p =
  try funs.program funs acc p
  with Fallback -> program funs acc p

and program funs acc { p_impl_list; p_index } =
  let n, acc = set_index_it funs acc p_index in
  let p_impl_list, acc = 
    Util.mapfold (implementation_it funs) acc p_impl_list in
  let p_index, acc = get_index_it funs acc n in
  { p_impl_list; p_index }, acc  

let rec interface_it global_funs acc interf =
  try global_funs.interface global_funs acc interf
  with Fallback -> interface global_funs acc interf

and interface global_funs acc interf = interf, acc

let default_global_funs =
  { build;
    var_ident;
    typevar;
    typeconstr;
    kind;
    type_expression;
    typedecl;
    interface;
  }

let defaults =
  { global_funs = default_global_funs;
    pattern;
    write_t;
    leq_t;
    equation;
    scondpat;
    size_t;
    expression;
    vardec;
    block;
    result;
    funexp;
    last;
    implementation;
    program;
    get_index;
    set_index;
    open_t;
  }
                 
let default_global_stop =
  { build = stop;
    var_ident = stop;
    typevar = stop;
    typeconstr = stop;
    kind = stop;
    type_expression = stop;
    typedecl = stop;
    interface = stop;
  }
let defaults_stop =
  { global_funs = default_global_stop;
    pattern = stop;
    write_t = stop;
    leq_t = stop;
    equation = stop;
    scondpat = stop;
    size_t = stop;
    expression = stop;
    vardec = stop;
    block = stop;
    result = stop;
    funexp = stop;
    last = stop;
    implementation = stop;
    program = stop;
    get_index = stop;
    set_index = stop;
    open_t = stop;
  }
  
