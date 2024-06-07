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

(** reduce static expressions *)

open Misc
open Ident
open Lident
open Ast
open Monad
open Opt
open Result

(** Build a renaming from an environment *)
let build env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  Env.fold buildrec env (Env.empty, Env.empty)
    
let rename n env = Env.find n env

(** Renaming of patterns *)
let rec pattern f acc ({ pat_desc } as p) =
  let pat_desc, acc = match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> pat_desc, acc
    | Evarpat(v) ->
       let v, acc = f acc v in
       Evarpat(v, acc)
    | Etuplepat(p_list) ->
       let p_list, acc = Utils.mapfold (pattern f) acc p_list in
       Etuplepat(p_list), acc
    | Econstr1pat(c, p_list) ->
       let p_list, acc = Utils.mapfold (pattern f) acc p_list in
       Econstr1pat(c, p_list), acc
    | Erecordpat(n_p_list) ->
       let n_p_list =
         Utils.mapfold 
           (fun acc { label; arg } ->
             let p, acc = pattern f p in
             { label; arg = pattern p}, acc) n_p_list in
       Erecordpat(n_p_list), acc
    | Ealiaspat(p1, n) ->
       let p1, acc = pattern f p1 in
       let n, acc = f acc n in
       Ealiaspat(p1, n), acc
    | Eorpat(p1, p2) ->
       let p1, acc = pattern f acc p1 in
       let p2, acc = pattern f acc p2 in
       Eorpat(p1, p2), acc
    | Etypeconstraintpat(p1, ty) ->
       let p1, acc = pattern f acc p1 in
       Etypeconstraintpat(p1, ty), acc in
  { p with pat_desc }, acc

(** Simplify an expression. This is mainly symbolic execution. Either the *)
(** result is a value or a term *)
(* [expression genv env e = v] *)
(* - genv is a global environment; *)
(* - env is an environment *)
let rec expression genv env ({ e_desc } as e) =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e
  | Evar(x) -> { e with e_desc = Evar(rename env x) }
  | Elast(x) -> { e with e_desc = Elast(rename env x) }
  | Etuple(e_list) ->
     { e with e_desc = List.map (expression genv env) e_list }
  | Econstr1 { lname; arg_list } ->
     let arg_list = List.map (expression genv env) arg_list in
     { e with e_desc = Econstr1 { lname; arg_list } }
  | Erecord(l_e_list) -> 
      let l_e_list =
        List.map (fun { label; arg } ->
            let arg = expression genv env arg in { label; arg }) l_e_list in
      { e with e_desc = Erecord(l_e_list) }
  | Erecord_access { label; arg } ->
      let arg = expression genv env arg in
      { e with e_desc = Erecord_access { label; arg } }
  | Erecord_with(e_record, l_e_list) -> 
     let e_record = expression genv env e_record in
     let l_e_list =
       List.map
	  (fun { label; arg } ->
            let arg = expression genv env e in { label; arg }) l_e_list in
      { e with e_desc = Erecord_with(e_record, l_e_list) }
  | Eapp ({ is_inline; f; arg_list } as a) ->
      if is_inline then
        (* [f] must be a transparent value and a closure *)
        let env = value_env env in
        try
          let f = vexp genv venv f in
          match f with
          | Value(Closure { c_funexp = { f_args; f_body }; c_genv; c_env }) ->
             (* local x1,...,xm do
                  p1 = e1 and ... pn = en and eq in
                x1,...,xm *)
             let arg_list = List.map (expression genv env) arg_list in
             let f_args, env = build_renaming env f_args in
             let eq_list =
               List.map
                 (fun (p_arg, arg) -> Aux.equation p_arg arg) f_args arg_list in
             let r = result genv env f_body in
             let vdec_list, eq, vdec_result = result f_body in
             Aux.local vdec_list (eq :: eq_list) vdec_result
          | _ -> raise Error
        with
          Unbound -> raise Error
      else
        let f = expression genv env f in
        let arg_list = List.map (expression genv env) arg_list in
        { e_desc = Eapp { a with f; arg_list } }
  | Eop(op, e_list) ->
     let e_list = List.map (expression genv env) e_list in
     { e with e_desc = Eop(op, e_list) }
  | Etypeconstraint(e_ty, ty) ->
     let e_ty = expression genv env e_ty in
     { e with e_desc = Etypeconstraint(e_ty, ty) }
  | Elet(l, e_let) ->
     let l, env = leq genv env l in
     let e_let = expression genv env e_let in
     { e with e_desc = Elet(l, e_let) }
  | Elocal(eq_b, e) ->
     let v, env = block genv env e in
     let e = expression genv env e in
     { e with e_desc = Elocal(eq_b, e) }
  | Epresent _ | Ematch _ -> assert false
        
(** Simplify a local declaration *)
and local venv (renaming, fun_defs) ({ l_eq = eq_list; l_env = env } as l) =
  let env, renaming0 = build env in
  let venv = remove renaming0 venv in
  let renaming = Env.append renaming0 renaming in
  let eq_list, fun_defs =
    Zmisc.map_fold (equation venv renaming) fun_defs eq_list in
  { l with l_eq = eq_list; l_env = env }, (renaming, fun_defs)

(** Simplify an equation. *)
and equation venv renaming fun_defs ({ eq_desc = desc } as eq) = 
  let desc, fun_defs =
    match desc with
    | EQeq(p, e) ->
        let p = pattern venv renaming p in
        let e, fun_defs = expression venv renaming fun_defs e in
        EQeq(p, e), fun_defs
    | EQpluseq(x, e) ->
        let e, fun_defs = expression venv renaming fun_defs e in
        EQpluseq(rename x renaming, e), fun_defs
    | EQinit(x, e) ->
        let e, fun_defs =
          expression venv renaming fun_defs e in
        EQinit(rename x renaming, e), fun_defs
    | EQnext(x, e, e_opt) ->
        let e, fun_defs = expression venv renaming fun_defs e in
        let e_opt, fun_defs =
          Zmisc.optional_with_map (expression venv renaming) fun_defs e_opt in
        EQnext(rename x renaming, e, e_opt), fun_defs
    | EQder(x, e, e_opt, p_e_list) ->
        let body fun_defs ({ p_cond = scpat; p_body = e; p_env = env } as p_e) =
          let env, renaming0 = build env in
          let venv = remove renaming0 venv in
          let renaming = Env.append renaming0 renaming in
          let scpat, fun_defs = scondpat venv renaming fun_defs scpat in
          let e, fun_defs = expression venv renaming fun_defs e in
          { p_e with p_cond = scpat; p_body = e; p_env = env }, fun_defs in
        let e, fun_defs = expression venv renaming fun_defs e in
        let e_opt, fun_defs =
          Zmisc.optional_with_map (expression venv renaming) fun_defs e_opt in
        let p_e_list, fun_defs = Zmisc.map_fold body fun_defs p_e_list in
        EQder(rename x renaming, e, e_opt, p_e_list), fun_defs
    | EQmatch(total, e, m_b_list) ->
        let body venv fun_defs ({ m_pat = p; m_body = b; m_env = env } as m_h) =
          let env, renaming0 = build env in
          let venv = remove renaming0 venv in
          let renaming = Env.append renaming0 renaming in
          let b, (_, fun_defs) = block venv (renaming, fun_defs) b in
	  { m_h with m_pat = pattern venv renaming p;
	      m_body = b; m_env = env }, fun_defs in
        let e, fun_defs = expression venv renaming fun_defs e in
        let m_b_list, fun_defs =
          Zmisc.map_fold (body venv) fun_defs m_b_list in
        EQmatch(total, e, m_b_list), fun_defs
    | EQblock(b) ->
        let b, (_, fun_defs) = block venv (renaming, fun_defs) b in
        EQblock(b), fun_defs
    | EQreset(eq_list, e) ->
        let e, fun_defs = expression venv renaming fun_defs e in
        let eq_list, fun_defs =
          Zmisc.map_fold (equation venv renaming) fun_defs eq_list in
        EQreset(eq_list, e), fun_defs
    | EQand(and_eq_list) ->
        let and_eq_list, fun_defs =
          Zmisc.map_fold (equation venv renaming) fun_defs and_eq_list in
        EQand(and_eq_list), fun_defs
    | EQbefore(before_eq_list) ->
        let before_eq_list, fun_defs =
          Zmisc.map_fold (equation venv renaming) fun_defs before_eq_list in
        EQbefore(before_eq_list), fun_defs
    | EQpresent(p_h_list, b_opt) ->
        let body fun_defs ({ p_cond = scpat; p_body = b; p_env = env } as p_b) =
          let env, renaming0 = build env in
          let venv = remove renaming0 venv in
          let renaming = Env.append renaming0 renaming in
          let scpat, fun_defs = scondpat venv renaming fun_defs scpat in
          let b, (renaming, fun_defs) = block venv (renaming, fun_defs) b in
          { p_b with p_cond = scpat; p_body = b; p_env = env }, fun_defs in
        let p_h_list, fun_defs = Zmisc.map_fold body fun_defs p_h_list in
        let b_opt, (_, fun_defs) =
          Zmisc.optional_with_map (block venv) (renaming, fun_defs) b_opt in
        EQpresent(p_h_list, b_opt), fun_defs
    | EQemit(x, e_opt) ->
        let e_opt, fun_defs =
          Zmisc.optional_with_map (expression venv renaming) fun_defs e_opt in
        EQemit(rename x renaming, e_opt), fun_defs
  | EQautomaton(is_weak, s_h_list, se_opt) ->
     let build_state_names renaming { s_state = { desc = desc } } =
       match desc with
       | Estate0pat(n) | Estate1pat(n, _) ->
	   let m = Zident.fresh (Zident.source n) in
           Env.add n m renaming in
     let statepat renaming ({ desc = desc } as spat) =
	 match desc with
	 | Estate0pat(x) -> { spat with desc = Estate0pat(rename x renaming) }
	 | Estate1pat(x, x_list) ->
	    let x = rename x renaming in
	    let x_list = List.map (fun x -> rename x renaming) x_list in
	    { spat with desc = Estate1pat(x, x_list) } in
     let state_exp venv renaming fun_defs ({ desc = desc } as se) =
       match desc with
       | Estate0(x) -> { se with desc = Estate0(rename x renaming) }, fun_defs
       | Estate1(x, e_list) ->
	  let e_list, fun_defs =
	    Zmisc.map_fold (expression venv renaming) fun_defs e_list in
	  { se with desc = Estate1(rename x renaming, e_list) }, fun_defs in
     let escape venv renaming fun_defs
         ({ e_cond = scpat; e_block = b_opt;
	    e_next_state = se; e_env = env } as esc) =
       let env, renaming0 = build env in
       let venv = remove renaming0 venv in
       let renaming = Env.append renaming0 renaming in
       let renaming, fun_defs, b_opt =
	 match b_opt with
         | None -> renaming, fun_defs, None
         | Some(b) ->
	     let b, (renaming, fun_defs) = block venv (renaming, fun_defs) b
             in renaming, fun_defs, Some(b) in
       let scpat, fun_defs = scondpat venv renaming fun_defs scpat in
       let se, fun_defs = state_exp venv renaming fun_defs se in
       { esc with e_cond = scpat; e_block = b_opt; e_next_state = se;
                  e_env = env },
       fun_defs in
     let body venv renaming fun_defs
         ({ s_state = spat; s_body = b; s_trans = esc_list;
            s_env = env } as h) =
       let env, renaming0 = build env in
       let venv = remove renaming0 venv in
       let renaming = Env.append renaming0 renaming in
       let spat = statepat renaming spat in
       let b, (renaming, fun_defs) = block venv (renaming, fun_defs) b in
       let esc_list, fun_defs =
	 Zmisc.map_fold (escape venv renaming) fun_defs esc_list in
       { h with s_state = spat; s_body = b; s_trans = esc_list; s_env = env },
       fun_defs in
     let renaming =
       List.fold_left build_state_names renaming s_h_list in
     let s_h_list, fun_defs =
       Zmisc.map_fold (body venv renaming) fun_defs s_h_list in
     let se_opt, fun_defs =
       Zmisc.optional_with_map (state_exp venv renaming) fun_defs se_opt in
     EQautomaton(is_weak, s_h_list, se_opt), fun_defs
  | EQforall({ for_index = i_list; for_init = init_list;
               for_body = b_eq_list;
	       for_in_env = in_env; for_out_env = out_env } as f_body ) ->
      let in_env, renaming0 = build in_env in
      let venv = remove renaming0 venv in
      let out_env, renaming1 = build out_env in
      let venv = remove renaming1 venv in
      let renaming = Env.append renaming0 (Env.append renaming1 renaming) in
      let index fun_defs ({ desc = desc } as ind) =
        let desc, fun_defs =
          match desc with
          | Einput(x, e) ->
	      let e, fun_defs = expression venv renaming fun_defs e in
              Einput(rename x renaming, e), fun_defs
          | Eoutput(x, xout) ->
              Eoutput(rename x renaming, rename xout renaming), fun_defs
          | Eindex(x, e1, e2) ->
	      let e1, fun_defs = static venv fun_defs e1 in
              let e2, fun_defs = static venv fun_defs e2 in
              Eindex(rename x renaming, e1, e2), fun_defs in
        { ind with desc = desc }, fun_defs in
     let init fun_defs ({ desc = desc } as ini) =
       let desc, fun_defs =
         match desc with
         | Einit_last(x, e) ->
	     let e, fun_defs = expression venv renaming fun_defs e in
             Einit_last(rename x renaming, e), fun_defs in
       { ini with desc = desc }, fun_defs in
     let i_list, fun_defs =
       Zmisc.map_fold index fun_defs i_list in
     let init_list, fun_defs =
       Zmisc.map_fold init fun_defs init_list in
     let b_eq_list, (_, fun_defs) = block venv (renaming, fun_defs) b_eq_list in
      EQforall { f_body with
                 for_index = i_list;
	         for_init = init_list;
	         for_body = b_eq_list;
		 for_in_env = in_env;
                 for_out_env = out_env }, fun_defs in
  { eq with eq_desc = desc; eq_write = Deftypes.empty }, fun_defs

and scondpat venv renaming fun_defs ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     let scpat1, fun_defs = scondpat venv renaming fun_defs scpat1 in
     let scpat2, fun_defs = scondpat venv renaming fun_defs scpat2 in
     { scpat with desc = Econdand(scpat1, scpat2) }, fun_defs
  | Econdor(scpat1, scpat2) ->
     let scpat1, fun_defs = scondpat venv renaming fun_defs scpat1 in
     let scpat2, fun_defs = scondpat venv renaming fun_defs scpat2 in
     { scpat with desc = Econdor(scpat1, scpat2) }, fun_defs
  | Econdexp(e) ->
     let e, fun_defs = expression venv renaming fun_defs e in
     { scpat with desc = Econdexp(e) }, fun_defs
  | Econdpat(e, p) ->
     let e, fun_defs = expression venv renaming fun_defs e in
     { scpat with desc = Econdpat(e, pattern venv renaming p) }, fun_defs
  | Econdon(scpat, e) ->
     let scpat, fun_defs = scondpat venv renaming fun_defs scpat in
     let e, fun_defs = expression venv renaming fun_defs e in
     { scpat with desc = Econdon(scpat, e) }, fun_defs

and vardec renaming ({ vardec_name = n } as v) =
    { v with vardec_name = rename n renaming }
  
and block venv (renaming, fun_defs)
    ({ b_vars = n_list; b_locals = l_list; b_body = eq_list;
       b_env = n_env } as b) =
  let n_env, renaming0 = build n_env in
  let venv = remove renaming0 venv in
  let renaming = Env.append renaming0 renaming in
  let n_list = List.map (vardec renaming) n_list in
  let l_list, (renaming, fun_defs) =
    Zmisc.map_fold (local venv) (renaming, fun_defs) l_list in
  let eq_list, fun_defs =
    Zmisc. map_fold (equation venv renaming) fun_defs eq_list in
  { b with b_vars = n_list; b_locals = l_list; 
           b_body = eq_list; b_write = Deftypes.empty; b_env = n_env },
  (renaming, fun_defs)

(** Convert a value into an expression. *)
(* [exp_of_value fun_defs v = acc', e] where
 * - fun_defs is a set of global function declarations;
 * - v is a value;
 * - e is the corresponding expression for v *)
and exp_of_value fun_defs { value_exp = v; value_name = opt_name } =
  let desc, fun_defs =
    match v with
    | Vconst(i) -> Econst(i), fun_defs
    | Vconstr0(qualident) ->
       Econstr0(Lident.Modname(qualident)), fun_defs
    | Vtuple(v_list) ->
       let v_list, fun_defs =
	 Zmisc.map_fold exp_of_value fun_defs v_list in
       Etuple(v_list), fun_defs
    | Vconstr1(qualident, v_list) ->
       let v_list, fun_defs =
	 Zmisc.map_fold exp_of_value fun_defs v_list in
       Econstr1(Lident.Modname(qualident), v_list), fun_defs
    | Vrecord(l_v_list) ->
       let l_e_list, fun_defs =
	 Zmisc.map_fold
	   (fun fun_defs (qid, v) ->
	    let v, fun_defs = exp_of_value fun_defs v in
	    (Lident.Modname(qid), v), fun_defs)
	   fun_defs l_v_list in
       Erecord(l_e_list), fun_defs
    | Vperiod { p_phase = p1; p_period = p2 } ->
       let p1, fun_defs =
         Zmisc.optional_with_map exp_of_value fun_defs p1 in
       let p2, fun_defs = exp_of_value fun_defs p2 in
       Eperiod { p_phase = p1; p_period = p2 }, fun_defs
    | Vabstract(qualident) ->
       Zaux.global (Lident.Modname(qualident)), fun_defs
    | Vfun(funexp, venv) ->
       (* if the function already exist, return its name *)
       match opt_name with
       | Some(qualident) ->
	  Zaux.global (Lident.Modname(qualident)), fun_defs
       | None ->
	  let funexp, fun_defs = lambda venv fun_defs funexp in
	  (* introduce a new function *)
	  let name = gfresh () in
	  Zaux.global (Lident.Name(name)),
	  { fundefs = (name, funexp) :: fun_defs.fundefs } in
    Zaux.emake desc Deftypes.no_typ, fun_defs
				     
(* Reduction under a function body. *)
and lambda venv fun_defs
    ({ f_args = p_list; f_body = e; f_env = env } as funexp) =
  let env, renaming = build env in
  let venv = remove renaming venv in
  let p_list = List.map (pattern venv renaming) p_list in
  let e, fun_defs = expression venv renaming fun_defs e in
  { funexp with f_args = p_list; f_body = e; f_env = env }, fun_defs

(* The main function. Reduce every definition *)
let implementation_list ff impl_list =
  let set_value_code name v =
    let ({ info = info } as entry) =
      try Modules.find_value (Lident.Name(name))
      with Not_found ->
	let qualname = Modules.qualify name in
	let info = Global.value_desc false Deftypes.no_typ_scheme qualname in
	Modules.add_value name info; { qualid = qualname; info = info } in
    Global.set_value_code entry v in

  (* convert a function declaration into an implementation phrase *)
  (* add every entry in the global symbol table once it has been typed *)
  let make (name, funexp) impl_defs =
    set_value_code name (value_code (Vfun(funexp, Env.empty)));
    Zaux.make (Efundecl(name, funexp)) :: impl_defs in

  (* [fun_defs] is the list of extra functions that have been introduced *)
  let implementation impl_defs impl = 
    match impl.desc with
    | Econstdecl(f, is_static, e) ->
       (* is [is_static = true], f is a compile-time constant *)
       let e, { fundefs = fun_defs } =
         if is_static then
           try
             let v = Static.expression Env.empty e in
             (* add [f \ v] in the global symbol table *)
             let v = Global.value_name (Modules.qualify f) v in
             set_value_code f v;
             exp_of_value empty v
           with
             Static.Error _ -> expression Env.empty Env.empty empty e
         else expression Env.empty Env.empty empty e in
       { impl with desc = Econstdecl(f, is_static, e) } ::
	 List.fold_right make fun_defs impl_defs
    | Efundecl(f, funexp) ->
       let ({ info = { value_typ = tys } } as entry) =
	 try Modules.find_value (Lident.Name(f))
	 with Not_found -> assert false in
       let no_parameter = Ztypes.noparameters tys in
       (* strong reduction (under the lambda) when [no_parameter] *)
       if !Zmisc.no_reduce then
	 (* no reduction is done; use it carefully as the compilation steps *)
	 (* done after like static scheduling may fail. *)
	 (* This flag is very temporary *)
	 let v = Global.value_code (Global.Vfun(funexp, Env.empty)) in
	 let v = Global.value_name (Modules.qualify f) v in
	 set_value_code f v;
	 impl :: impl_defs
       else
	 let funexp, impl_defs =
	   if no_parameter then
	     let funexp, { fundefs = fun_defs } = lambda Env.empty empty funexp in
	     funexp, { impl with desc = Efundecl(f, funexp) } ::
		       List.fold_right make fun_defs impl_defs
           else
             (* funexp is removed from the list of defs. to be compiled *)
	     funexp, impl_defs in
	 let v = Global.value_code (Global.Vfun(funexp, Env.empty)) in
	 let v = Global.value_name (Modules.qualify f) v in
	 set_value_code f v;
	 impl_defs
    | _ -> impl :: impl_defs in
  try
    let impl_list = List.fold_left implementation [] impl_list in
    List.rev impl_list
  with
  | Static.Error(error) ->
      match error with
      | TypeError ->
          Format.eprintf
            "@[Internal error (static reduction):@,\
             the expression to be reduced is not static.@.@]";
          raise Zmisc.Error
      | NotStaticExp(e) ->
          Format.eprintf
            "@[%aInternal error (static reduction):@,\
             static evaluation failed because the expression is not static.@.@]"
            Printer.expression e;
          raise Zmisc.Error
      | NotStaticEq(eq) ->
          Format.eprintf
            "@[%aInternal error (static reduction):@,\
             static evaluation failed because the equation is not static.@.@]"
            Printer.equation eq;
          raise Zmisc.Error


(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)
(* Generic mapred over Heptagon AST *)

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
   to the [hep_it_funs] field (corresponding to the Heptagon AST type).  There
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
     let (eq, acc) = Hept_mapfold.eq funs acc eq in
     ...
     (eq, acc)
   ]

   The record provided here and the functions to iterate over any type
   ([type_it]) enable lots of different ways to deal with the AST.

   Discover it by yourself !*)

(* /!\ Do not EVER put in your funs record one of the generic iterator function
   [type_it]. You should always put a custom version or the default version
   provided in this file. Trespassers will loop infinitely! /!\ *)

(*
open Misc
open Errors
open Global_mapfold
open Heptagon

type 'a it_funs = {
  app            : 'a hept_it_funs -> 'a -> app -> app * 'a;
  block          : 'a hept_it_funs -> 'a -> block -> block * 'a;
  edesc          : 'a hept_it_funs -> 'a -> desc -> desc * 'a;
  eq             : 'a hept_it_funs -> 'a -> eq -> eq * 'a;
  eqdesc         : 'a hept_it_funs -> 'a -> eqdesc -> eqdesc * 'a;
  escape_unless  : 'a hept_it_funs -> 'a -> escape -> escape * 'a;
  escape_until   : 'a hept_it_funs -> 'a -> escape -> escape * 'a;
  exp            : 'a hept_it_funs -> 'a -> exp -> exp * 'a;
  pat            : 'a hept_it_funs -> 'a -> pat -> pat * 'a;
  present_handler: 'a hept_it_funs -> 'a -> present_handler -> present_handler * 'a;
  state_handler  : 'a hept_it_funs -> 'a -> state_handler -> state_handler * 'a;
  switch_handler : 'a hept_it_funs -> 'a -> switch_handler -> switch_handler * 'a;
  var_dec        : 'a hept_it_funs -> 'a -> var_dec -> var_dec * 'a;
  last           : 'a hept_it_funs -> 'a -> last -> last * 'a;
  objective      : 'a hept_it_funs -> 'a -> objective -> objective * 'a;
  contract       : 'a hept_it_funs -> 'a -> contract -> contract * 'a;
  node_dec       : 'a hept_it_funs -> 'a -> node_dec -> node_dec * 'a;
  const_dec      : 'a hept_it_funs -> 'a -> const_dec -> const_dec * 'a;
  program        : 'a hept_it_funs -> 'a -> program -> program * 'a;
  program_desc   : 'a hept_it_funs -> 'a -> program_desc -> program_desc * 'a;
  global_funs    : 'a Global_mapfold.global_it_funs }


let rec exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let e_desc, acc = edesc_it funs acc e.e_desc in
  let e_ty, acc = ty_it funs.global_funs acc e.e_ty in
  let e_ct_annot, acc = optional_wacc (ct_it funs.global_funs) acc e.e_ct_annot in
  let e_level_ck, acc = ck_it funs.global_funs acc e.e_level_ck in
  { e with e_desc = e_desc; e_ty = e_ty; e_ct_annot = e_ct_annot; e_level_ck = e_level_ck }, acc

and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Econst se ->
      let se, acc = static_exp_it funs.global_funs acc se in
      Econst se, acc
  | Evar v ->
      let v, acc = var_ident_it funs.global_funs acc v in
      Evar v, acc
  | Elast v ->
      let v, acc = var_ident_it funs.global_funs acc v in
      Elast v, acc
  | Epre (se, e) ->
      let se, acc = optional_wacc (static_exp_it funs.global_funs) acc se in
      let e, acc = exp_it funs acc e in
      Epre (se, e), acc
  | Efby (e1, e2) ->
      let e1, acc = exp_it funs acc e1 in
      let e2, acc = exp_it funs acc e2 in
      Efby (e1,e2), acc
  | Estruct n_e_list ->
      let aux acc (n,e) =
        let e, acc = exp_it funs acc e in
        (n,e), acc in
      let n_e_list, acc = mapfold aux acc n_e_list in
      Estruct n_e_list, acc
  | Eapp (app, args, reset) ->
      let app, acc = app_it funs acc app in
      let args, acc = mapfold (exp_it funs) acc args in
      let reset, acc = optional_wacc (exp_it funs) acc reset in
      Eapp (app, args, reset), acc
  | Eiterator (i, app, params, pargs, args, reset) ->
      let app, acc = app_it funs acc app in
      let params, acc = mapfold (static_exp_it funs.global_funs) acc params in
      let pargs, acc = mapfold (exp_it funs) acc pargs in
      let args, acc = mapfold (exp_it funs) acc args in
      let reset, acc = optional_wacc (exp_it funs) acc reset in
      Eiterator (i, app, params, pargs, args, reset), acc
  | Ewhen (e, c, n) ->
      let e, acc = exp_it funs acc e in
      let n, acc = var_ident_it funs.global_funs acc n in
      Ewhen (e, c, n), acc
  | Emerge (n, c_e_list) ->
      let n, acc = var_ident_it funs.global_funs acc n in
      let aux acc (c,e) =
        let e, acc = exp_it funs acc e in
        (c,e), acc
      in
      let c_e_list, acc = mapfold aux acc c_e_list in
      Emerge (n, c_e_list), acc
  | Esplit (e1, e2) ->
      let e1, acc = exp_it funs acc e1 in
      let e2, acc = exp_it funs acc e2 in
        Esplit(e1, e2), acc

and app_it funs acc a = funs.app funs acc a
and app funs acc a =
  let p, acc = mapfold (static_exp_it funs.global_funs) acc a.a_params in
  { a with a_params = p }, acc


and pat_it funs acc p =
  try funs.pat funs acc p
  with Fallback -> pat funs acc p
and pat funs acc p = match p with
  | Etuplepat pl ->
      let pl, acc = mapfold (pat_it funs) acc pl in
      Etuplepat pl, acc
  | Evarpat v ->
      let v, acc = var_ident_it funs.global_funs acc v in
      Evarpat v, acc


and eq_it funs acc eq = funs.eq funs acc eq
and eq funs acc eq =
  let eqdesc, acc = eqdesc_it funs acc eq.eq_desc in
  { eq with eq_desc = eqdesc }, acc


and eqdesc_it funs acc eqd =
  try funs.eqdesc funs acc eqd
  with Fallback -> eqdesc funs acc eqd
and eqdesc funs acc eqd = match eqd with
  | Eautomaton st_h_l ->
      let st_h_l, acc = mapfold (state_handler_it funs) acc st_h_l in
      Eautomaton st_h_l, acc
  | Eswitch (e, sw_h_l) ->
      let e, acc = exp_it funs acc e in
      let sw_h_l, acc = mapfold (switch_handler_it funs) acc sw_h_l in
      Eswitch (e, sw_h_l), acc
  | Epresent (p_h_l, b) ->
      let p_h_l, acc = mapfold (present_handler_it funs) acc p_h_l in
      let b, acc = block_it funs acc b in
      Epresent (p_h_l, b), acc
  | Ereset (b, e) ->
      let b, acc = block_it funs acc b in
      let e, acc = exp_it funs acc e in
      Ereset (b, e), acc
  | Eblock b ->
      let b, acc = block_it funs acc b in
      Eblock b, acc
  | Eeq (p, e) ->
      let p, acc = pat_it funs acc p in
      let e, acc = exp_it funs acc e in
      Eeq (p, e), acc


and block_it funs acc b = funs.block funs acc b
and block funs acc b =
  let b_local, acc = mapfold (var_dec_it funs) acc b.b_local in
  let b_equs, acc = mapfold (eq_it funs) acc b.b_equs in
  let b_defnames, acc =
    Idents.Env.fold
      (fun v v_dec (env,acc) ->
         let v, acc = var_ident_it funs.global_funs acc v in
         let v_dec, acc = var_dec_it funs acc v_dec in
         let env = Idents.Env.add v v_dec env in
         env, acc)
      b.b_defnames
      (Idents.Env.empty, acc) in
  { b with b_local = b_local; b_equs = b_equs; b_defnames = b_defnames }, acc


and state_handler_it funs acc s = funs.state_handler funs acc s
and state_handler funs acc s =
  let s_unless, acc = mapfold (escape_unless_it funs) acc s.s_unless in
  let s_block, acc = block_it funs acc s.s_block in
  let s_until, acc = mapfold (escape_until_it funs) acc s.s_until in
  { s with s_block = s_block; s_until = s_until; s_unless = s_unless }, acc


(** escape is a generic function to deal with the automaton state escapes,
    still the iterator function record differentiate until and unless
    with escape_until_it and escape_unless_it *)
and escape_unless_it funs acc esc = funs.escape_unless funs acc esc
and escape_until_it funs acc esc = funs.escape_until funs acc esc
and escape funs acc esc =
  let e_cond, acc = exp_it funs acc esc.e_cond in
  { esc with e_cond = e_cond }, acc


and switch_handler_it funs acc sw = funs.switch_handler funs acc sw
and switch_handler funs acc sw =
  let w_block, acc = block_it funs acc sw.w_block in
  { sw with w_block = w_block }, acc


and present_handler_it funs acc ph = funs.present_handler funs acc ph
and present_handler funs acc ph =
  let p_cond, acc = exp_it funs acc ph.p_cond in
  let p_block, acc = block_it funs acc ph.p_block in
  { p_cond = p_cond; p_block = p_block }, acc

and var_dec_it funs acc vd = funs.var_dec funs acc vd
and var_dec funs acc vd =
  let v_type, acc = ty_it funs.global_funs acc vd.v_type in
  let v, acc = var_ident_it funs.global_funs acc vd.v_ident in
  let v_clock, acc = ck_it funs.global_funs acc vd.v_clock in
  let v_last, acc = last_it funs acc vd.v_last in
  { vd with v_last = v_last; v_type = v_type; v_clock = v_clock; v_ident = v }, acc


and last_it funs acc l =
  try funs.last funs acc l
  with Fallback -> last funs acc l
and last funs acc l = match l with
  | Var -> l, acc
  | Last sto ->
      let sto, acc = optional_wacc (static_exp_it funs.global_funs) acc sto in
      Last sto, acc


and objective_it funs acc o = funs.objective funs acc o
and objective funs acc o =
  let e, acc = exp_it funs acc o.o_exp in
  { o with o_exp = e }, acc

and contract_it funs acc c = funs.contract funs acc c
and contract funs acc c =
  let c_assume, acc = exp_it funs acc c.c_assume in
  let c_objectives, acc = mapfold (objective_it funs) acc c.c_objectives in
  let c_assume_loc, acc = exp_it funs acc c.c_assume_loc in
  let c_enforce_loc, acc = exp_it funs acc c.c_enforce_loc in
  let c_block, acc = block_it funs acc c.c_block in
  let c_controllables, acc = mapfold (var_dec_it funs) acc c.c_controllables in
  { c_assume = c_assume;
    c_objectives = c_objectives;
    c_assume_loc = c_assume_loc;
    c_enforce_loc = c_enforce_loc;
    c_block = c_block;
    c_controllables = c_controllables },
  acc

and param_it funs acc vd = funs.param funs acc vd
and param funs acc vd =
  let v_last, acc = last_it funs acc vd.v_last in
  { vd with v_last = v_last }, acc

and node_dec_it funs acc nd =
  Idents.enter_node nd.n_name;
  funs.node_dec funs acc nd
and node_dec funs acc nd =
  let n_input, acc = mapfold (var_dec_it funs) acc nd.n_input in
  let n_output, acc = mapfold (var_dec_it funs) acc nd.n_output in
  let n_params, acc = mapfold (param_it funs.global_funs) acc nd.n_params in
  let n_contract, acc =  optional_wacc (contract_it funs) acc nd.n_contract in
  let n_block, acc = block_it funs acc nd.n_block in
  { nd with
      n_input = n_input;
      n_output = n_output;
      n_block = n_block;
      n_params = n_params;
      n_contract = n_contract }
  , acc


and const_dec_it funs acc c = funs.const_dec funs acc c
and const_dec funs acc c =
  let c_type, acc = ty_it funs.global_funs acc c.c_type in
  let c_value, acc = static_exp_it funs.global_funs acc c.c_value in
  { c with c_value = c_value; c_type = c_type }, acc

and program_it funs acc p = funs.program funs acc p
and program funs acc p =
  let p_desc, acc = mapfold (program_desc_it funs) acc p.p_desc in
  { p with p_desc = p_desc }, acc

and program_desc_it funs acc pd =
  try funs.program_desc funs acc pd
  with Fallback -> program_desc funs acc pd
and program_desc funs acc pd = match pd with
  | Pconst cd -> let cd, acc = const_dec_it funs acc cd in Pconst cd, acc
  | Ptype _td -> pd, acc (* TODO types *)
  | Pnode n -> let n, acc = node_dec_it funs acc n in Pnode n, acc

let defaults = {
  app = app;
  block = block;
  edesc = edesc;
  eq = eq;
  eqdesc = eqdesc;
  escape_unless = escape;
  escape_until = escape;
  exp = exp;
  pat = pat;
  present_handler = present_handler;
  state_handler = state_handler;
  switch_handler = switch_handler;
  var_dec = var_dec;
  last = last;
  objective = objective;
  contract = contract;
  node_dec = node_dec;
  const_dec = const_dec;
  program = program;
  program_desc = program_desc;
  global_funs = Global_mapfold.defaults }



let defaults_stop = {
  app = stop;
  block = stop;
  edesc = stop;
  eq = stop;
  eqdesc = stop;
  escape_unless = stop;
  escape_until = stop;
  exp = stop;
  pat = stop;
  present_handler = stop;
  state_handler = stop;
  switch_handler = stop;
  var_dec = stop;
  last = stop;
  objective = stop;
  contract = stop;
  node_dec = stop;
  const_dec = stop;
  program = stop;
  program_desc = stop;
  global_funs = Global_mapfold.defaults_stop }
 *)
