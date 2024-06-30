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

(* Functions to build terms *)
(* Invariant: variables defined by an equation (writes) must be correct *)

open Misc
open Location
open Zelus
open Ident
open Lident
open Initial
open Deftypes

let defnames eq_list =
  List.fold_left (fun acc { eq_write } -> Defnames.union eq_write acc)
    Defnames.empty eq_list

let desc e = e.desc
let make x = { desc = x; loc = no_location }

let emake desc =
  { e_desc = desc; e_loc = no_location; e_info = no_info }
let pmake desc =
  { pat_desc = desc; pat_loc = no_location; pat_info = no_info }


let global lname = Eglobal { lname = lname }
let const c = emake (Econst c)
let constr0 lname = emake (Econstr0 { lname })
let constr1 lname arg_list = emake (Econstr1 { lname; arg_list })
let evoid = const Evoid
let efalse = const (Ebool(false))
let etrue = const (Ebool(true))
let truepat = pmake (Econstpat(Ebool(true)))
let falsepat = pmake (Econstpat(Ebool(false)))
let wildpat = pmake (Ewildpat)
let zero = emake (Econst(Efloat(0.0)))
let one = emake (Econst(Efloat(1.0)))
let minus_one = emake (Econst(Efloat(-1.0)))
let infinity = emake (global (Modname(Initial.stdlib_name "infinity")))
let tuplepat pat_list = pmake (Etuplepat(pat_list))
let tuple e_list = emake (Etuple(e_list))
let record l_list e_list =
  emake (Erecord(List.map2 (fun label arg -> { label; arg }) l_list e_list))
let ifthenelse e e_true e_false =
  emake (Eop(Eifthenelse, [e_true; e_false]))

let eqmake w desc =
  { eq_desc = desc; eq_loc = no_location; eq_write = w }

let pat_make x =
  { pat_desc = Evarpat(x); pat_loc = no_location; pat_info = no_info }

let eq_make p e =
  let w = { Defnames.empty with dv = Write.fv_pat S.empty p } in
  eqmake w (EQeq(p, e))

let id_eq id e =
  let w = Defnames.singleton id in
  eqmake w (EQeq(pat_make id, e))

let wildpat_eq e =
  eqmake Defnames.empty (EQeq(wildpat, e))

let eq_init id e =
  let eq = eqmake (Defnames.singleton id) (EQinit(id, e)) in
  let eq, _ = Write.equation eq in eq

let eq_der id e =
  let w = { Defnames.empty with der = S.singleton id } in
  eqmake w (EQder { id; e; e_opt = None; handlers = [] })

let eq_and eq1 eq2 =
  let w = Defnames.union eq1.eq_write eq2.eq_write in
  eqmake w (EQand [eq1; eq2])

let par eq_list =
  match eq_list with
  | [] -> assert false
  | [eq] -> eq
  | _ -> eqmake (defnames eq_list) (EQand(eq_list))

let vardec id var_is_last var_init var_default =
  { var_name = id; var_is_last; var_init; var_default; var_clock = false;
    var_typeconstraint = None; var_loc = no_location }

let block_make vardec_list eq_list =
  let b_body =
    match eq_list with
    | [] -> eqmake Defnames.empty EQempty
    | [eq] -> eq
    | _ -> par eq_list in
  let b = { b_vars = vardec_list; b_env = Env.empty; b_loc = no_location;
            b_write = Defnames.empty; b_body } in
  let w = defnames eq_list in
  let def = List.fold_left
              (fun acc { var_name } -> S.add var_name acc) S.empty vardec_list in
  let w = Defnames.diff w def in
{ b with b_write = w }

let eq_reset eq e = eqmake eq.eq_write (EQreset(eq, e))
let eq_match is_total e handlers =
  let w = List.fold_left
            (fun acc { m_body = { eq_write } } -> Defnames.union eq_write acc)
            Defnames.empty handlers in
  eqmake w (EQmatch { is_total; e; handlers })
let eq_present handlers default_opt =
  let w = List.fold_left
            (fun acc { p_body = { eq_write } } -> Defnames.union eq_write acc)
            Defnames.empty handlers in
  let w =
    match default_opt with
    | NoDefault -> w | Init(eq) | Else(eq) -> Defnames.union eq.eq_write w in
  eqmake w (EQpresent { handlers; default_opt })
    
let eq_local b = eqmake b.b_write (EQlocal(b))

let match_handler p b =
  { m_pat = p; m_body = b; m_env = Env.empty;
    m_reset = false; m_zero = false; m_loc = no_location }

let eq_ifthenelse e eq_true eq_false =
  let w = Defnames.union eq_true.eq_write eq_false.eq_write in
  eqmake w (EQif { e; eq_true; eq_false })

let eq_ifthen e eq_true =
  let eq_empty = eqmake Defnames.empty EQempty in
  eq_ifthenelse e eq_true eq_empty
    
let rec eq_let_list leq_list eq =
  match leq_list with
  | [] -> eq
  | leq :: leq_list -> eq_let leq (eq_let_list leq_list eq)

and eq_let leq eq =
  eqmake eq.eq_write (EQlet(leq, eq))
    
let pat_of_vardec_make { var_name } = pat_make var_name

let pat_of_vardec_list_make vardec_list =
  match vardec_list with
  | [] -> pmake Ewildpat
  | _ -> pmake (Etuplepat(List.map pat_of_vardec_make vardec_list))

let eq_of_f_arg_arg_make f_arg arg =
  let p = pat_of_vardec_list_make f_arg in
  eq_make p arg

let eq_local b = eqmake b.b_write (EQlocal(b))

let returns_of_vardec_make { var_name } = emake (Evar(var_name))

let returns_of_vardec_list_make vardec_list =
  match vardec_list with
  | [] -> emake (Econst(Evoid))
  | _ -> emake (Etuple(List.map returns_of_vardec_make vardec_list))

let e_present handlers default_opt =
   emake (Epresent { handlers; default_opt })
let e_match is_total e handlers =
  emake (Ematch { is_total; e; handlers })

let e_local b e = emake (Elocal(b, e))

let eq_ifthen e eq_true =
  let eq_empty = eqmake Defnames.empty EQempty in
  eq_ifthenelse e eq_true eq_empty

let rec orpat pat_list =
  match pat_list with
    | [] -> assert false
    | [pat] -> pat
    | pat :: pat_list -> pmake (Eorpat(pat, orpat pat_list))

let varpat name = pmake (Evarpat(name))
let var name = emake (Evar(name))

let pair e1 e2 =  emake (Etuple([e1; e2]))
let pairpat p1 p2 = pmake (Etuplepat([p1; p2]))

let patalias p n = pmake (Ealiaspat(p, n))
let last x = emake (Elast(x))
let float v = emake (Econst(Efloat(v)))
let bool v = emake (Econst(Ebool(v)))

let global_in_stdlib lname =
  emake (global (Modname(Initial.stdlib_name lname)))

let unop op e =
  emake (Eapp { is_inline = false; f = global_in_stdlib op; arg_list = [e] })
let binop op e1 e2 =
  emake (Eapp { is_inline = false; f = global_in_stdlib op;
                arg_list = [e1;e2] })

let plus e1 e2 = binop "+." e1 e2
let minus e1 e2 = binop "-." e1 e2
let diff e1 e2 = binop "<>" e1 e2
let or_op e1 e2 = binop "||" e1 e2
let and_op e1 e2 = binop "&&" e1 e2
let on_op e1 e2 = binop "on" e1 e2
let min_op e1 e2 = binop "min" e1 e2
let greater_or_equal e1 e2 = binop ">=" e1 e2
let greater e1 e2 = binop ">" e1 e2
let up e = emake (Eop(Eup, [e]))
let pre e = emake (Eop(Eunarypre, [e]))
let minusgreater e1 e2 = emake (Eop(Eminusgreater, [e1;e2]))
let fby e1 e2 = emake (Eop(Efby, [e1;e2]))
let ifthenelse e1 e2 e3 =
  emake (Eop(Eifthenelse, [e1;e2;e3]))
let sgn e =
  ifthenelse (greater e zero) one minus_one
let record_access arg label = emake (Erecord_access { arg; label })
    
(* find the major step in the current environment *)
(* If it already exist in the environment *)
(* returns it. Otherwise, create one *)
let new_major env =
  let m = Ident.fresh "major" in
  let env =
    Env.add m { t_path = [];
                t_sort = Deftypes.major (); t_typ = Initial.typ_bool } env in
  let major = var m in
  env, major
	 
let major env =
  let exception Return of no_info Zelus.exp in
  let find x t =
    match t with
    | { t_sort = Sort_mem { m_kind = Some(Major) }; t_typ = typ } ->
       raise (Return(var x))
    | _ -> () in
  try
    Env.iter find env;
    new_major env
  with
  | Return(x) -> env, x 

