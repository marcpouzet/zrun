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

(* type definition *)

open Misc
open Lident

type name = string

(* types *)
type 'a loc =
  { mutable t_desc: 'a;   (* descriptor *)
    mutable t_index: int; (* a number for debugging purpose *)
    mutable t_level: int; (* level for generalisation *)
  }

type typ = typ_desc loc

and typ_desc =
  | Tvar
  | Tproduct of typ list
  | Tconstr of Lident.qualident * typ list * abbrev ref
  | Tvec of typ * size
  | Tsize of is_singleton * size
  | Tarrow of kind * typ * typ 
  | Tlink of typ

and is_singleton = bool

and size = size_desc loc

and size_desc =
  | Sconst of int
  | Svar
  | Sop of op * size * size
  | Slink of size

and op = Splus | Sminus | Smult

and abbrev =
  | Tnil
  | Tcons of typ list * typ

(* type scheme *)
and typ_scheme =
    { typ_vars: typ list;
      size_vars: size list;
      mutable typ_body: typ }
	
and typ_instance = { typ_instance : typ list }

and kind =
  | Tfun : vkind -> kind (* combinatorial expression *)
  | Tnode : tkind -> kind (* stateful expression *)

and vkind =
  | Tconst (* value known at compile time *)
  | Tstatic (* value known at instantiation time *)
  | Tany (* dynamically know value *)

and tkind =
  | Tdiscrete (* contains discrete-time state variables *)
  | Thybrid (* contains continuous-time state variables *)

(* entry in the typing environment *)
type 'a tentry = 
  { t_path : tsort list; (* [k1 on ... on kn x : t] *)
    mutable t_sort: tsort; (* sort *)
    mutable t_default: 'a option; (* default value *)
    mutable t_init: 'a minit; (* init value *)
    mutable t_typ: typ (* its type *)
  }

and tsort =
  | Sort_const (* a variable whose value is known at compile time *)
  | Sort_static (* the value is known at instantiation time *)
  | Sort_val (* a let variable *)
  | Sort_var (* a shared variable *)
  | Sort_mem : { m_kind: mkind } -> tsort (* a state variable *)

and 'a minit =
  | NoInit (* no initialisation given *)
  | InitEq (* the initial value is given in the body of equations *)
  | InitDecl of 'a (* it is given at the declaration point *)

(* the different kinds of internal state variables *)
and mkind =
  | Discrete (* discrete state variable *)
  | Cont (* continous state variable *)
  | Zero (* zero-crossing *)

(* generic and non generic variables in the various type systems *)
let generic = -1
let notgeneric = 0
let maxlevel = max_int

let binding_level = ref 0
let top_binding_level () = !binding_level = 0

let push_binding_level () = binding_level := !binding_level + 1
let pop_binding_level () =
  binding_level := !binding_level - 1;
  assert (!binding_level > generic)
let reset_binding_level () = binding_level := 0

(* making types *)
let make ty =
  { t_desc = ty; t_level = generic; t_index = Genames.symbol#name }
let product ty_list =
  make (Tproduct(ty_list))
let vec ty e = make (Tvec(ty, e))
let const v = make (Sconst(v))
let size is_singleton si = make (Tsize(is_singleton, si))
let op o si1 si2 = make (Sop(o, si1, si2))
let arrowtype k ty_arg ty_res =
  make (Tarrow(k, ty_arg, ty_res))
let rec arrowtype_list k ty_arg_list ty_res =
  match ty_arg_list with
  | [] -> ty_res
  | ty :: ty_arg_list ->
     arrowtype k ty (arrowtype_list k ty_arg_list ty_res)
                  
let constr name ty_list abbrev = make (Tconstr(name, ty_list, abbrev))
let nconstr name ty_list = constr name ty_list (ref Tnil)

let new_size_var () =
  { t_desc = Svar; t_level = !binding_level; t_index = Genames.symbol#name }
let new_generic_size_var () =
  { t_desc = Svar; t_level = generic; t_index = Genames.symbol#name }

let new_var () =
  { t_desc = Tvar; t_level = !binding_level; t_index = Genames.symbol#name }
let new_generic_var () =
  { t_desc = Tvar; t_level = generic; t_index = Genames.symbol#name }
let rec new_var_list n =
  match n with
    0 -> []
  | n -> (new_var ()) :: new_var_list (n - 1)
let forall l typ_body = { size_vars = []; typ_vars = l; typ_body = typ_body }
