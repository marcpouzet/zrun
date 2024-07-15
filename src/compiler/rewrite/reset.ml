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

(* Static expressions - simple sufficient condition for [e] to be static *)
let rec static { e_desc } =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> true
  | Etuple(e_list) -> List.for_all static e_list
  | Erecord(qual_e_list) ->
     List.for_all (fun { arg } -> static arg) qual_e_list
  | Erecord_access { arg } -> static arg
  | _ -> false

(* the initialization variable *)
type acc = { init : Ident.t option }

let empty = { init = None }

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

(* Equations *)
let rec equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQinit(_, e) when static e -> eq, acc
  | EQinit(x, e) ->
     let e, acc = expression funs acc e in
     reset_init acc { eq with eq_desc = EQinit(x, e) }
  | EQmatch { e; handlers } ->
     let body acc ({ m_body } as m_h) =
       (* introduce one init per branch *)
       let m_body, _ = equation funs empty m_body in
       { m_h with m_body = local_in_eq acc m_body }, acc in
     let e, acc = expression funs acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
       { eq with eq_desc = EQmatch { is_total = true; e; handlers } }, acc
  | EQreset(eq, e) ->
     let e, acc = expression funs acc e in
     (* introduce one init per branch *)
     let eq, acc = equation funs empty eq in
     { eq with eq_desc = EQreset(local_in_eq acc eq, e) }, acc       
  | _ -> Mapfold.equation funs acc eq

(** Expressions. *)
and expression funs acc ({ e_desc } as e) =
  match e_desc with
  | Eop(Eminusgreater, [e1; e2]) ->
     let e1, acc = expression funs acc e1 in
     let e2, acc = expression funs acc e2 in
     (* [if last i then e1 else e2] *)
     ifthenelse acc e1 e2
     (* [if last i then e1 else e2] *)
  | Ematch({ e; handlers } as m) ->
     let body acc ({ m_body } as m_h) =
       (* introduce one init per branch *)
       let m_body, _ = expression funs empty m_body in
       { m_h with m_body = local_in_exp acc m_body }, acc in
     let e, acc = expression funs acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
     { e with e_desc = Ematch { m with e; handlers } }, acc
  | Ereset(e, e_r) ->
     let e_r, acc = expression funs acc e_r in
     (* introduce one init per branch *)
     let e, acc = expression funs empty e in
     { e with e_desc = Ereset(local_in_exp acc e, e_r) }, acc       
  | _ -> Mapfold.expression funs acc e

let result funs acc ({ r_desc } as r) =
  (* introduce one init per branch *)
  let r_desc, acc = match r_desc with
  | Exp(e) ->
     let e, _ = expression funs empty e in
     Exp(local_in_exp acc e), acc
  | Returns({ b_vars; b_body } as b) ->
     let b_body, acc = equation funs empty b_body in
     Returns { b with b_vars; b_body = local_in_eq acc b_body }, acc in
  { r with r_desc }, acc
  
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; equation; result;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

