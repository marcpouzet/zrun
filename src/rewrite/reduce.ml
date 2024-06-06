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

(** reduce expressions that are tagged to be static; leave other unchanged *)

open Misc
open Ident
open Lident
open Ast

type 'a env = { r_env: Ident.t Ident.Env.t; (* renaming *)
                v_env: 'a Ident.Env.t; (* values *)
              }

(** Build a renaming from an environment *)
let build env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  Env.fold buildrec env (Env.empty, Env.empty)
    
let rename n env = Env.find n env

(** Renaming of patterns *)
let pattern f p = 
  let rec pattern ({ pat_desc } as p) =
    let pat_desc = match pat_desc with
      | Ewildpat | Econstpat _ | Econstr0pat _ -> pat_desc
      | Evarpat(n) ->  Evarpat(f n)
      | Etuplepat(p_list) -> Etuplepat(List.map pattern p_list)
      | Econstr1pat(c, p_list) ->
         Econstr1pat(c, List.map pattern p_list)
      | Erecordpat(n_p_list) ->
         let n_p_list =
           List.map 
             (fun { label; arg } -> { label; arg = pattern p}) n_p_list in
         Erecordpat(n_p_list)
      | Ealiaspat(p1, n) ->
         Ealiaspat(pattern p1, f n)
      | Eorpat(p1, p2) ->
         Eorpat(pattern p1, pattern p2)
      | Etypeconstraintpat(p1, ty) ->
         Etypeconstraintpat(pattern p1, ty) in
    { p with pat_desc } in
  pattern p

(** Simplify an expression. This is mainly symbolic execution. Either the *)
(* result is a close value or a value in which some leaves are variables *)
(* [expression venv renaming fun_defs e = e', fun_defs'] *)
(* - venv an environment of values;
 *- renaming is a renaming of variables;
 *- e and e' are expressions;
 *- fun_defs and fun_defs' are list of the functions introduced 
 *- during the simplification 
*)
let rec expression env ({ e_desc } as e) =
  match e_desc with
  | Econst(v) -> 
     Value(immediate v)
  | Econstr0 { lname } ->
     Value(Vconstr0(lname))
  | Eglobal { lname } ->
     let v = find_gvalue_opt lname genv |>
         Opt.to_result ~none:{ kind = Eunbound_lident(lname); loc = e_loc } in
     Value(v)
  | Evar(x) -> 
     find_value_opt x env |> Opt.to_result ~none: e
  | Elast _ | Eperiod _ -> e
  | Etuple(e_list) ->
      let e_list = List.map (expression env) e_list in
      { e with e_desc = Etuple(e_list) }
  | Econstr1 { lname; arg_list } ->
      let arg_list = List.map (expression env) arg_list in
     { e with e_desc = Econstr1 { lname; arg_list } }
  | Erecord(l_e_list) -> 
      let l_e_list =
        List.map
	  (fun { label; arg } -> 
            let arg = expression env arg in { label; arg })
          l_e_list in
      { e with e_desc = Erecord(l_e_list) }
  | Erecord_access { label; arg } ->
      let arg = expression env arg in
      { e with e_desc = Erecord_access { label; arg } }
  | Erecord_with(e_record, l_e_list) -> 
     let e_record = expression env e_record in
     let l_e_list =
       List.map
	  (fun { label; arg } ->
            let arg = expression env e in { label; arg }) l_e_list in
      { e with e_desc = Erecord_with(e_record, l_e_list) }
  | Eapp ({ is_inline; f; arg_list } as a) ->
      let arg_list = List.map (expression env) arg_list in
      let f = expression env f in
      if is_inline then
        (* [f] must be a transparent value that is a closure *)
      else
        (* [e_fun] is necessarily static. It needs to be a compile-time *)
      (* non opaque value only when [inline] is true *)
      (* [e_list] decomposes into (a possibly empty) sequence of 
       *- static arguments [s_list] and non static ones [ne_list] *)
      let e, fun_defs =
        let s_list, ne_list, ty_res =
          Ztypes.split_arguments e_fun.e_typ e_list in
        let ne_list, fun_defs =
          Zmisc.map_fold (expression venv renaming) fun_defs ne_list in
        try
          let v_fun = Static.expression venv e_fun in
          let { value_exp = v; value_name = opt_name } as v_fun =
            Static.app v_fun (List.map (Static.expression venv) s_list) in
          match ne_list with
          | [] ->
	      let e, fun_defs = exp_of_value fun_defs v_fun in
              { e with e_typ = ty_res }, fun_defs
          | _ ->
	      (* two solutions are possible. Either we introduce a fresh *)
              (* function [f] for the result of [v_fun s1...sn] *)
              (* and return [f ne1...nek]. [f] could then be shared in case *)
              (* several instance of [v_fun s1...sn] exist *)
	      (* Or we directly inline the body of [f]. We take this solution *)
	      (* for the moment *)
              match opt_name, v with
              | None,
                Vfun({ f_args = p_list; f_body = e; f_env = f_env },
                     venv_closure) ->
	          (* [p_list] should now be a list of non static parameters *)
                  let f_env, renaming0 = build f_env in
                  let venv = remove renaming0 venv in
                  let renaming = Env.append renaming0 renaming in
                  let p_list = List.map (pattern venv renaming) p_list in
                  let e, fun_defs =
                    expression venv_closure renaming fun_defs e in
	          (* return [let p1 = ne1 in ... in pk = nek in e] *)
	          Zaux.make_let f_env
                    (List.map2
                     (fun p ne -> Zaux.eqmake (EQeq(p, ne))) p_list ne_list) e,
                    fun_defs
	      | _ -> (* returns an application *)
                  let e_fun, fundefs = exp_of_value fun_defs v_fun in
	          let e_fun = { e_fun with e_typ = ty_res } in
	          { e with e_desc = Eapp(app, e_fun, ne_list) }, fun_defs
        with
          Static.Error _ ->
            let e_fun, fun_defs = expression venv renaming fun_defs e_fun in
            let s_list, fun_defs =
              Zmisc.map_fold (expression venv renaming) fun_defs s_list in
            { e with e_desc = Eapp(app, e_fun, s_list @ ne_list) }, fun_defs in
      e, fun_defs
  | Eop(op, e_list) ->
      let e_list, fun_defs =
        Zmisc.map_fold (expression venv renaming) fun_defs e_list in
     { e with e_desc = Eop(op, e_list) }, fun_defs
  | Etypeconstraint(e_ty, ty) ->
      let e_ty, fun_defs =
        expression venv renaming fun_defs e_ty in
      let ty = type_expression venv renaming ty in
      { e with e_desc = Etypeconstraint(e_ty, ty) }, fun_defs
  | Eseq(e1, e2) ->
      let e1, fun_defs =
        expression venv renaming fun_defs e1 in
      let e2, fun_defs =
        expression venv renaming fun_defs e2 in
     { e with e_desc = Eseq(e1, e2) }, fun_defs
  | Elet(l, e_let) ->
     let l, (renaming, fun_defs) = local venv (renaming, fun_defs) l in
     let e_let, fun_defs =
       expression venv renaming fun_defs e_let in
     { e with e_desc = Elet(l, e_let) }, fun_defs
  | Eblock(b, e_block) ->
      let b, (renaming, fun_defs) = block venv (renaming, fun_defs) b in
      let e_block, fun_defs = expression venv renaming fun_defs e_block in
      { e with e_desc = Eblock(b, e_block) }, fun_defs
  | Epresent _ | Ematch _ -> assert false

(* evaluate a static expression [e] at compile-time if possible *)
(* and turn it into an expression. Otherwise, returns [e] *)
(* preserve the type of [e].  *)
and static venv fun_defs e =
  try
    let v = Static.expression venv e in
    let { e_desc = desc }, fun_defs = exp_of_value fun_defs v in
    { e with e_desc = desc }, fun_defs
  with
    Static.Error _ -> e, fun_defs
                      
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
