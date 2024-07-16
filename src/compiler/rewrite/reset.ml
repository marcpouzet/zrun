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

(* removes the initialization operator [e1 -> e2] *)
(* This operator is equivalent to [if (true fby false) then e1 else e2] *)
(* that is [if last* i then e1 else e2] with [init i = true and i = false] *)
(* An initialization register [i] with [init i = true and i = false] *)
(* is introduced for every control block *)
(* every initialisation [init x = e] where [e] is not static is reseted *)
(* on an initialization bit; it is rewritten [reset init x = e every last* i] *)

open Misc
open Location
open Ident
open Zelus
open Mapfold

(*
  [e1 -> e2] is rewritten in [if last* i then e1 else e2]
  adding a declaration [local i init true do i = false and ...] around

  [reset
   ... init x = e ... (* [e] is static *)
   every z]

  is unchanged

  [reset
   ... init x = e ... (* [e] is not static *)
   every z

   is rewritten:

   reset
   ... local i init true and i = false and 
       reset init x = e every last* i
   ...
   every z]

   match e with
   | P1 -> eq1 | ... | Pn -> eqn

   is rewritten:

   match e with
   | P1 -> local i1 init true and i1 = false and eq1
   | ...
   | Pn -> local in init true and in = false and eqn
*)

let fresh () = Ident.fresh "i"

(* the initialization variable *)
type acc = { init : Ident.t option }

let empty = { init = None }

(* Static expressions - simple sufficient condition for [e] to be static *)
let rec static { e_desc } =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> true
  | Etuple(e_list) -> List.for_all static e_list
  | Erecord(qual_e_list) ->
     List.for_all (fun { arg } -> static arg) qual_e_list
  | Erecord_access { arg } -> static arg
  | _ -> false

let intro { init } =
  let id = match init with | None -> fresh () | Some(id) -> id in
  id, { init = Some(id) }

(* [e1 -> e2] translated into [if last id then e1 else e2] *)
let ifthenelse acc e1 e2 =
  let id, acc = intro acc in
  Aux.emake (Eop(Eifthenelse, [Aux.last_star id; e1; e2])), acc

(* Surround an equation by a reset *)
let reset_init acc eq =
  let id, acc = intro acc in
  Aux.eq_reset eq (Aux.last_star id), acc

(* [local i init true in do i = false and eq done] *)
let local_in_eq { init } eq =
  match init with
  | None -> eq
  | Some(id) ->
     Aux.eq_local (Aux.block_make [Aux.vardec id false (Some(Aux.etrue)) None]
                  [Aux.eq_and (Aux.id_eq id Aux.efalse) eq])

(* [local m init true, i do m = false and i = last* m in e] *)
let local_in_exp { init } e =
  match init with
  | None -> e
  | Some(id) ->
     let m = fresh () in
     Aux.e_local
       (Aux.block_make [Aux.vardec m false (Some(Aux.etrue)) None;
                        Aux.vardec id false None None]
          [Aux.id_eq id (Aux.last_star m); Aux.id_eq m (Aux.efalse)]) e

let reset_eq funs acc eq =
  let eq, acc_local = Mapfold.equation_it funs empty eq in
  local_in_eq acc_local eq, acc

let reset_e funs acc e =
  let e, acc_local = Mapfold.expression_it funs empty e in
  local_in_exp acc_local e, acc

let match_handler_eq funs acc ({ m_body } as m_h) =
  let m_body, acc = reset_eq funs acc m_body in 
  { m_h with m_body }, acc

and match_handler_e funs acc ({ m_body } as m_h) =
  let e, acc = reset_e funs empty m_body in 
  { m_h with m_body }, acc

and present_handler_eq funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body, acc = reset_eq funs acc p_body in
  { p_b with p_cond; p_body }, acc

and present_handler_e funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body, acc = reset_e funs acc p_body in
  { p_b with p_cond; p_body }, acc

and if_eq funs acc (eq_true, eq_false) =
  let eq_true, acc = reset_eq funs acc eq_true in
  let eq_false, acc = reset_eq funs acc eq_false in
  (eq_true, eq_false), acc

(* Equations *)
let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQinit(_, e) when static e -> eq, acc
  | EQinit(x, e) ->
     let e, acc = Mapfold.expression_it funs acc e in
     reset_init acc { eq with eq_desc = EQinit(x, e) }
  | _ -> raise Mapfold.Fallback

(** Expressions. *)
let expression funs acc { e_desc } =
  match e_desc with
  | Eop(Eminusgreater, [e1; e2]) ->
     let e1, acc = Mapfold.expression_it funs acc e1 in
     let e2, acc = Mapfold.expression_it funs acc e2 in
     (* [if last i then e1 else e2] *)
     ifthenelse acc e1 e2
     (* [if last i then e1 else e2] *)
  | _ -> raise Mapfold.Fallback

let result funs acc ({ r_desc } as r) =
  (* introduce one init per branch *)
  let r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc = reset_e funs acc e in
       Exp(e), acc
  | Returns({ b_vars; b_body } as b) ->
     let b_vars, acc =
       Util.mapfold (Mapfold.vardec_it funs) acc b_vars in
     let b_body, acc = reset_eq funs acc b_body in
     Returns { b with b_vars; b_body }, acc in
  { r with r_desc }, acc
  
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; equation; result;
                            reset_e; reset_eq; match_handler_eq;
                            match_handler_e; present_handler_eq;
                            present_handler_e; if_eq;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

