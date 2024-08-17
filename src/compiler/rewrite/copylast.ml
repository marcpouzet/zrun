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

(* This pass is necessary for static scheduling. *)
(* For every local variable [x] that is not an input nor output *)
(* such that [last x] is used *)
(* add an equation [lx = last* x] and replace [last x] by [lx] *)

(*
  Example:

  local (last x), (last y), z init e
  do init x = v0 and init y = v1 and ... y = last x + 1 and
  ... x = last y + 1 and ... z ...

  is rewritten:

  local lx, (last x), ly, (last y) do
  init x = v0 and init y = v1
  ly = last* y
  lx = last* x
  y = lx + 1
  x = ly + 1
*)

(* For input/output variables (e.g., variables in patterns), they must be values only *)
(* Any expression [last x] where [x] is expected to be a value *)
(* is rewritten [last* m and m = x] are introduced *)

(* Example:
 *- [let node f(x) = ... last x...] is rewritten
 *- [let node f(x) = local (last m), r do r = ... last* m and m = x in r]
 *- [let node f(x) returns (...y...) ...last x... last y ...] is rewritten
 *- [let node f(x) returns (...y...) ... last* m ... last* my ... m = x ... my = y]
 *- [match e with P(...x...) -> ...last x...] is rewritten
 *- [match e with P(...x...) -> local (last m) ...last* m... and m = x]
 *- [present e(...x...) -> ... last x ...] is rewritten
 *- [present e(...x...) -> local (last m) do r = ... last* m and m = x in r]
 *- [present e(...x...) -> ... last x ...] is rewritten
 *- [present e(...x...) -> local (last m) ... last* m and m = x]
*)

open Location
open Zelus
open Ident
open Defnames
open Aux

(* renaming(x) = lx for [x] in [out_names] *)
type acc =
  { locals: Misc.no_info Env.t; 
    (* names that are defined locally in a block. They are neither inputs *)
    (* or outputs but introduced by a [local ... x ... do ... ] *)
    renaming: Ident.t Env.t; (* renaming [x -> m] *)
  }

let empty = { locals = Env.empty; renaming = Env.empty }

(* split [renaming] in two according to [l_env]. Returns [l_renaming] *)
(* and [r_renaming] such that [renaming = l_renaming + r_renaming] *)
(* and [Names(l_renaming) subset Names(l_env)] *)
let split l_env renaming =
  Env.fold
    (fun x lx (l_renaming, r_renaming) ->
       if Env.mem x l_env then Env.add x lx l_renaming, r_renaming
       else l_renaming, Env.add x lx r_renaming)
    renaming (Env.empty, Env.empty)
    
let update_env l_env l_renaming =
  Env.fold (fun x lx acc -> Env.add lx Misc.no_info acc) l_renaming l_env

(* Make an equation [lx = last* x] *)
let add_last_eq_copy l_renaming =
  let copy lx x = Aux.id_eq lx (Aux.last_star x) in
  Env.fold (fun x lx acc -> copy lx x :: acc) l_renaming []

let copy m x = Aux.id_eq m (Aux.var x)

let add_eq_copy l_renaming acc =
  Env.fold (fun x m acc -> copy m x :: acc) l_renaming acc

(* update a local declaration [local x...] into [local lx, x...] *)
(* an equation [lx = last*x] is added in the body *)
let update_local_vardec_list b_vars l_renaming =
  List.fold_left
    (fun acc ({ var_name } as v) ->
      try let lx = Env.find var_name l_renaming in
          Aux.vardec lx false None None :: v :: acc
      with
      | Not_found -> v :: acc) [] b_vars

(* update a local declaration which is an input or output *)
(* remove [init ...] and [default ...] entries *)
let update_inout_vardec l_renaming (v_list, eq_list)
      ({ var_name; var_is_last; var_init; var_default; var_init_in_eq } as v) =
  try
    let m = Env.find var_name l_renaming in
    { v with var_is_last = false; var_init = None; var_default = None; 
             var_init_in_eq = false },
    (Aux.init_vardec m var_is_last var_init var_default var_init_in_eq ::
       v_list,
     copy m var_name :: eq_list)
  with
  | Not_found -> v, (v_list, eq_list)

(* add extra local declarations *)
let vardec_list l_renaming acc =
  Env.fold (fun x m acc -> Aux.vardec m true None None :: acc) l_renaming acc

let e_local l_renaming e = 
  if Env.is_empty l_renaming then e
  else let r = fresh "r" in
       Aux.e_local_vardec 
         (Aux.vardec r false None None :: vardec_list l_renaming [])
         (add_eq_copy l_renaming [Aux.id_eq r e]) (var r)

let eq_local l_renaming eq =
  Aux.eq_local_vardec (vardec_list l_renaming [])(add_eq_copy l_renaming [eq])

let intro ({ locals; renaming } as acc) id =
  try
    let lx = Env.find id renaming in lx, acc
  with
  | Not_found ->
     let lx = fresh "lx" in lx, { acc with renaming = Env.add id lx renaming }
                                             
(* replace every occurrence of [last x] where [x] is a local variable *)
(* by [lx]; an equation [lx = last*x] will be added. Otherwise *)
(* replace it by [last* lx]; an equation [x = lx] will be added *)
let expression funs ({ locals } as acc) ({ e_desc } as e) =
  match e_desc with
  | Elast { copy; id } ->
     if Env.mem id locals then
       if copy then
         let lx, acc = intro acc id in
         (* turn [last x] into [lx] *)
         var lx, acc
       else { e with e_desc = Elast { copy = false; id } }, acc
     else let lx, acc = intro acc id in
          { e with e_desc = Elast { copy = false; id = lx} }, acc
  | _ -> raise Mapfold.Fallback

(* add extra equations [lx = last* x]. *)
let leq_t funs ({ locals } as acc) ({ l_eq; l_env; l_rec } as leq) =
  let l_eq, { renaming } =
    Mapfold.equation
      funs { acc with locals = Env.append l_env locals } l_eq in
  (* add an equation [lx = last* x] for every [x\lx] in [renaming inter l_env] *)
  let l_renaming, renaming = split l_env renaming in
  (* the resulting equations are recursive if [l_rec] or *)
  (* at least one copy is added *)
  let l_rec = l_rec || not (Env.is_empty l_renaming) in
  { leq with l_eq = Aux.par (l_eq :: add_last_eq_copy l_renaming);
             l_env = update_env l_env l_renaming; l_rec },
  { locals; renaming }

(* if [last x] appears in the body with [x] a local variable *)
(* an extra equation [lx = last* x] is introduced. [lx] becomes a new *)
(* local variable *)
let block funs acc ({ b_vars; b_body; b_env } as b) =
  let b_vars, ({ locals } as acc) =
    Util.mapfold (Mapfold.vardec funs) acc b_vars in
  let b_body, ({ renaming } as acc) =
    Mapfold.equation funs { acc with locals = Env.append b_env locals } b_body in
  let l_renaming, renaming = split b_env renaming in
  { b with b_vars = update_local_vardec_list b_vars l_renaming;
           b_env = update_env b_env l_renaming;
           b_body = Aux.par (b_body :: add_last_eq_copy l_renaming) }, 
  { locals; renaming }

(* replace [init id = e] by [init m = e] when [m] is an *)
(* input/output variable. [acc.renaming id = m] *)
let init_ident _ ({ locals; renaming } as acc) id = 
  if Env.mem id locals then id, acc
  else intro acc id

let write_it funs ({ renaming } as acc) { dv; di; der } =
  let rename id = try Env.find id renaming with Not_found -> id in
  let dv = S.map rename dv in
  let di = S.map rename di in
  let der = S.map rename der in
  { dv; di; der }, acc
  
let match_handler_eq funs acc ({ m_body; m_env } as m_h) =
  let m_body, ({ renaming } as acc) = Mapfold.equation_it funs acc m_body in 
  let m_renaming, renaming = split m_env renaming in
  { m_h with m_body = eq_local m_renaming m_body }, acc

and match_handler_e funs acc ({ m_body; m_env } as m_h) =
  let m_body, ({ renaming } as acc) = Mapfold.expression_it funs acc m_body in 
  let m_renaming, renaming = split m_env renaming in
  { m_h with m_body = e_local m_renaming m_body }, acc

and present_handler_eq funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body, ({ renaming } as acc) = Mapfold.equation_it funs acc p_body in
  let p_renaming, renaming = split p_env renaming in
  { p_b with p_cond; p_body = eq_local p_renaming p_body }, acc

and present_handler_e funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body, ({ renaming } as acc) = Mapfold.expression_it funs acc p_body in
  let p_renaming, renaming = split p_env renaming in
  { p_b with p_cond; p_body = e_local p_renaming p_body }, acc

(* the inputs/outputs must be unchanged *)
let funexp funs ({ locals } as acc)
      ({ f_args; f_body = { r_desc } as r; f_env } as f) =
  let r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, ({ renaming } as acc) =
        Mapfold.expression funs acc e in
       let l_renaming, renaming = split f_env renaming in
       Exp(e_local l_renaming e), { acc with renaming }
    | Returns({ b_vars; b_body; b_env } as b) ->
       (* the interface must not change *)
       let b_vars, acc =
         Util.mapfold (Mapfold.vardec funs) acc b_vars in
       let b_body, ({ renaming } as acc) =
         Mapfold.equation funs acc b_body in
       let b_renaming, renaming = split b_env renaming in
       let b_vars, (v_list, eq_list) =
         Util.mapfold (update_inout_vardec b_renaming) ([], []) b_vars in
       let f_renaming, renaming = split f_env renaming in
       let b_body =
         (* add names for [last x] when [x] is an output *)
         Aux.eq_local_vardec v_list (b_body :: eq_list) in
       let b_body =
         (* add names for [last x] when [x] is an input *)
         eq_local f_renaming b_body in
       Returns { b with b_vars; b_body },
       { locals; renaming } in
  { f with f_body = { r with r_desc } }, acc

let pattern funs acc p = p, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = { Mapfold.default_global_funs with init_ident } in
  let funs =
    { Mapfold.defaults with pattern; expression; leq_t; block;
                            funexp; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
