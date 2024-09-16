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

(* Remove last in patterns *)
(* All variables in patterns must be values only                          *)
(* e.g., function parameters, patterns in pattern matching handlers, etc. *)
(* Any expression [last x] in an equation [eq] where [x] is expected to *)
(* be a value is rewritten [last* x] and [eq] replaced by *)
(* [local m do m = x and eq] *)

(* Example:
 *- [let node f(x) = ... last x...] is rewritten
 *- [let node f(m) = local x do x = m and ... last* x...]

 *- [let node f(...x init e1 default e0...) returns (...) ...last x] is rewritten
 *- [let node f(...m...) returns (...)
 *-       local x init ... default ... do x = m and ...last* x done]

 *- [let node f(...) returns (...x init ... default ...) ... last x ...] is rewritten
 *- [let node f(...) returns (...m ...)
       local x init ... default ... do m = x and ... last* x]

 *- [match e with P(...x...) -> eq] is rewritten
 *- [match e with P(...m...) -> 
       local x do x = m and eq[last* x \ last x]]
 *- [present
       e(...x...) -> eq] is rewritten
 *- [present
       e(...m...) ->
         local x do x = m and eq[last* x \ last x]]
 *)

           
open Zelus
open Ident

type acc =
  { env: Misc.no_info Env.t; (* environment of names *)
    renaming: Ident.t Env.t; (* renaming [x -> m] *)
  }

let empty = { env = Env.empty; renaming = Env.empty }

let build funs ({ env } as acc) l_env =
  env, { acc with env = Env.append l_env env }

let last_ident funs ({ env } as acc) ({ copy; id } as l) =
  let l = if Env.mem id env then { l with copy = false } else l in
  l, acc

(* rename a variable declaration *)
let vardec l_renaming (v_list, eq_list) ({ var_name } as v) =
  try
    let m = Env.find var_name l_renaming in
    Aux.vardec m false None None :: v_list,
    Aux.id_eq var_name (Aux.var m) :: eq_list
  with
  | Not_found -> v :: v_list, eq_list

(*
  (* [local r, x1,..., xn do r = e and x1 = m1 and ... and xn = mn in r] *)
let e_local_x_m l_renaming e = 
  if Env.is_empty l_renaming then e
  else let r = fresh "r" in
       Aux.e_local_vardec 
         (Aux.vardec r false None None :: vardec_list l_renaming [])
         (add_eq_copy l_renaming [Aux.id_eq r e]) (Aux.var r)

(* [local m1,...,mn do m1 = x1 and ... and mn = xn and eq done] *)
let eq_local_m_x l_renaming eq =
  if Env.is_empty l_renaming then eq
  else
    Aux.eq_local_vardec (vardec_list l_renaming []) (add_eq_copy l_renaming [eq])

(* Make equations [lx1 = last* x1 and ... lxn = last* xn] *)
(* from a [renaming] where [renaming(x) = lx] *)
let add_last_copy_eq l_renaming =
  let copy lx x = Aux.id_eq lx (Aux.last_star x) in
  Env.fold (fun x lx acc -> copy lx x :: acc) l_renaming []

(* add copy names in [l_env] *)
let add_copy_names_in_env l_env l_renaming =
  Env.fold (fun x lx acc -> Env.add lx Misc.no_info acc) l_renaming l_env

(* Make an equation [let lx1 = last* x1 and ... lx_n = last* xn in eq] *)
let eq_let_lx_lastx l_renaming eq =
  if Env.is_empty l_renaming then eq
  else let eq_list = add_last_copy_eq l_renaming in
       Aux.eq_let (Aux.leq eq_list) eq

(* Inject [let lx1 = last* x1 and ... lx_n = last* xn in eq] into a block *)
let block_let_lx_lastx l_renaming ({ b_body } as b) =
  { b with b_body = eq_let_lx_lastx l_renaming b_body }

let intro ({ locals; renaming } as acc) id =
  try
    let lx = Env.find id renaming in lx, acc
  with
  | Not_found ->
     let lx = fresh "lx" in lx, { acc with renaming = Env.add id lx renaming }
                                             
(* Given a [renaming] and an environment [l_env], decompose it in two *)
(* Returns [l_renaming] (for local renaming) and [r_renaming] (for *)
(* renaming that remains) such that [renaming = l_renaming + r_renaming] *)
(* [Names(l_renaming) subset Names(l_env)] *)
let extract_local_renaming l_env renaming =
  Env.fold
    (fun x lx (l_renaming, r_renaming) ->
       if Env.mem x l_env then Env.add x lx l_renaming, r_renaming
       else l_renaming, Env.add x lx r_renaming)
    renaming (Env.empty, Env.empty)
    
(* replace every occurrence of [last x] where [x] is a local variable *)
(* by [lx]; an equation [lx = last*x] will be added. Otherwise *)
(* replace it by [last* m]; an equation [x = m] will be added *)
let expression funs ({ locals } as acc) ({ e_desc } as e) =
  match e_desc with
  | Elast { copy; id } ->
     if Env.mem id locals then
       if copy then
         let lx, acc = intro acc id in
         (* turn [last x] into [lx] *)
         Aux.var lx, acc
       else e, acc
     else
       let m, acc = intro acc id in
       { e with e_desc = Elast { copy = false; id = m} }, acc
  | _ -> raise Mapfold.Fallback

(* add extra equations [lx = last* x] *)
let leq_t funs ({ locals } as acc) ({ l_eq; l_env; l_rec } as leq) =
  let l_eq, { renaming } =
    Mapfold.equation_it
      funs { acc with locals = Env.append l_env locals } l_eq in
  (* add an equation [lx = last* x] for every [x\lx] in [renaming inter l_env] *)
  let l_renaming, renaming = extract_local_renaming l_env renaming in
  (* the resulting equations are recursive if [l_rec] or *)
  (* at least one copy is added *)
  let l_rec = l_rec || not (Env.is_empty l_renaming) in
  { leq with l_eq = Aux.par (l_eq :: add_last_copy_eq l_renaming);
             l_env = add_copy_names_in_env l_env l_renaming; l_rec },
  { locals; renaming }

let block funs acc ({ b_vars; b_body; b_env } as b) =
  let b_vars, ({ locals } as acc) =
    Util.mapfold (Mapfold.vardec_it funs) acc b_vars in
  let b_body, ({ renaming } as acc) =
    Mapfold.equation_it
      funs { acc with locals = Env.append b_env locals } b_body in
  (* add extra equations [lx = last* x] *)
  let l_renaming, renaming = extract_local_renaming b_env renaming in
  { b with b_vars; b_body = eq_let_lx_lastx l_renaming b_body},
  { locals; renaming }

let for_returns funs acc { r_returns; r_block; r_env } =
  let r_returns, ({ locals } as acc) =
    Util.mapfold (Mapfold.for_vardec_it funs) acc r_returns in
  let { b_body } as r_block, ({ renaming } as acc) =
    Mapfold.block_it
      funs { acc with locals = Env.append r_env locals } r_block in
  let l_renaming, renaming = extract_local_renaming r_env renaming in
  { r_returns;
    r_block = { r_block with b_body = eq_let_lx_lastx l_renaming b_body };
    r_env }, acc

let for_exp_t funs acc for_body =
  match for_body with
  | Forexp { exp; default } ->
     let exp, acc = expression funs empty exp in
     let default, acc =
       Util.optional_with_map (expression funs) acc default in
     Forexp { exp; default }, acc
  | Forreturns(f) ->
     let f, acc = Mapfold.for_returns_it funs acc f in
     Forreturns f, acc

let for_eq_t funs ({ locals } as acc)
      ({ for_out; for_block; for_out_env } as for_eq) =
  let for_out, acc =
    Util.mapfold (Mapfold.for_out_it funs) acc for_out in
  let for_block, { renaming } =
    Mapfold.block_it
      funs { acc with locals = Env.append for_out_env locals } for_block in
  let l_renaming, renaming = extract_local_renaming for_out_env renaming in
  let for_block = block_let_lx_lastx l_renaming for_block in
  { for_eq with for_out; for_block }, { locals; renaming }

let for_out_t funs acc ({ desc = ({ for_init; for_default } as desc) } as f) =
  let for_init, acc =
    Util.optional_with_map (Mapfold.expression_it funs) acc for_init in
  let for_default, acc =
    Util.optional_with_map (Mapfold.expression_it funs) acc for_default in
  { f with desc = { desc with for_init; for_default } }, acc

let match_handler_eq funs acc ({ m_body; m_env } as m_h) =
  let m_body, ({ renaming } as acc) = Mapfold.equation_it funs acc m_body in 
  let m_renaming, renaming = extract_local_renaming m_env renaming in
  { m_h with m_body = eq_local_m_x m_renaming m_body }, acc

and match_handler_e funs acc ({ m_body; m_env } as m_h) =
  let m_body, ({ renaming } as acc) = Mapfold.expression_it funs acc m_body in 
  let m_renaming, renaming = extract_local_renaming m_env renaming in
  { m_h with m_body = e_local_m_x m_renaming m_body }, acc

and present_handler_eq funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body, ({ renaming } as acc) = Mapfold.equation_it funs acc p_body in
  let p_renaming, renaming = extract_local_renaming p_env renaming in
  { p_b with p_cond; p_body = eq_local_m_x p_renaming p_body }, acc

and present_handler_e funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body, ({ renaming } as acc) = Mapfold.expression_it funs acc p_body in
  let p_renaming, renaming = extract_local_renaming p_env renaming in
  { p_b with p_cond; p_body = e_local_m_x p_renaming p_body }, acc

(* the inputs/outputs must be unchanged *)
let funexp funs ({ locals } as acc) ({ f_args; f_body; f_env } as f) =
  let arg_t acc vardec_list =
    Util.mapfold (Mapfold.vardec_it funs) acc vardec_list in
  let f_args, acc = Util.mapfold arg_t acc f_args in
  let ({ r_desc } as r), ({ renaming } as acc) =
    Mapfold.result_it
      funs { acc with locals = Env.append f_env locals } f_body in
  let l_renaming, renaming = extract_local_renaming f_env renaming in
  let r_desc =
    match r_desc with
    | Exp(e) ->
       Exp(e_local_m_x l_renaming e)
    | Returns({ b_body } as b) ->
       Returns { b with b_body = eq_let_lx_lastx l_renaming b_body } in
  { f with f_args; f_body = { r with r_desc } }, acc

let pattern funs acc p = p, acc

 *)
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc


let program _ p =
  let global_funs = Mapfold.default_global_funs  in (* with init_ident } in *)
  let funs = 
    { Mapfold.defaults with (* pattern; expression; leq_t; block;
                            for_returns; for_exp_t; for_eq_t;
                            match_handler_eq; match_handler_e;
                            present_handler_eq; present_handler_e;
                            funexp; *) set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
