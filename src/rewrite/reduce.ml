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
    
let rename env n = Env.find n env, env

(** Renaming of patterns *)
let rec pattern f acc ({ pat_desc } as p) =
  let pat_desc, acc = match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> pat_desc, acc
    | Evarpat(v) ->
       let v, acc = f acc v in
       Evarpat(v), acc
    | Etuplepat(p_list) ->
       let p_list, acc = Util.mapfold (pattern f) acc p_list in
       Etuplepat(p_list), acc
    | Econstr1pat(c, p_list) ->
       let p_list, acc = Util.mapfold (pattern f) acc p_list in
       Econstr1pat(c, p_list), acc
    | Erecordpat(n_p_list) ->
       let n_p_list, acc =
         Util.mapfold 
           (fun acc { label; arg } ->
             let arg, acc = pattern f acc p in
             { label; arg}, acc) acc n_p_list in
       Erecordpat(n_p_list), acc
    | Ealiaspat(p1, n) ->
       let p1, acc = pattern f acc p1 in
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

(** Expressions **)
let rec expression acc ({ e_desc } as e) =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e, acc
  | Evar(x) ->
     let x, acc = rename acc x in
     { e with e_desc = Evar(x) }, acc
  | Elast(x) ->
     let x, acc = rename acc x in
     { e with e_desc = Elast(x) }, acc
  | Etuple(e_list) ->
     let e_list, acc = Util.mapfold expression acc e_list in
     { e with e_desc = Etuple(e_list) }, acc
  | Econstr1 { lname; arg_list } ->
     let arg_list, acc = Util.mapfold expression acc arg_list in
     { e with e_desc = Econstr1 { lname; arg_list } }, acc
  | Erecord(l_e_list) -> 
      let l_e_list, acc =
        Util.mapfold (fun acc { label; arg } ->
            let arg, acc = expression acc arg in 
            { label; arg }, acc) acc l_e_list in
      { e with e_desc = Erecord(l_e_list) }, acc
  | Erecord_access { label; arg } ->
      let arg, acc = expression acc arg in
      { e with e_desc = Erecord_access { label; arg } }, acc
  | Erecord_with(e_record, l_e_list) -> 
     let e_record, acc = expression acc e_record in
     let l_e_list, acc =
       Util.mapfold
	  (fun acc { label; arg } ->
            let arg, acc = expression acc e in { label; arg }, acc)
          acc l_e_list in
      { e with e_desc = Erecord_with(e_record, l_e_list) }, acc
  | Eapp ({ f; arg_list } as a) ->
     let f, acc = expression acc f in
     let arg_list, acc = Util.mapfold expression acc arg_list in
     { e with e_desc = Eapp { a with f; arg_list } }, acc
  | Eop(op, e_list) ->
     let e_list, acc = Util.mapfold expression acc e_list in
     { e with e_desc = Eop(op, e_list) }, acc
  | Etypeconstraint(e_ty, ty) ->
     let e_ty, acc = expression acc e_ty in
     { e with e_desc = Etypeconstraint(e_ty, ty) }, acc
  | Elet(l, e_let) ->
     let l, acc = leq acc l in
     let e_let, acc = expression acc e_let in
     { e with e_desc = Elet(l, e_let) }, acc
  | Elocal(eq_b, e) ->
     let eq_b, acc = block acc eq_b in
     let e, acc = expression acc e in
     { e with e_desc = Elocal(eq_b, e) }, acc
  | Epresent({ handlers; default_opt } as h) ->
     let body acc ({ p_cond; p_body; p_env } as p_b) =
       let p_env, acc = build acc p_env in
       let p_cond, acc = scondpat acc p_cond in
       let p_body, acc = expression acc p_body in
       { p_b with p_cond; p_body }, acc in
     let handlers, acc =
       Util.mapfold body acc handlers in
     let default_opt, acc = default_opt expression acc default_opt in
     { e_desc = Epresent { h with handlers; default_opt } }, acc 
  | Ematch({ e; handlers } as m) ->
     let body acc ({ m_pat; m_body; m_env } as m_h) =
       let m_env, acc = build acc m_env in
       let m_pat, acc = pattern acc m_pat in
       let m_body, acc = expression acc m_body in
       { m_h with m_pat; m_body; m_env }, acc in
     let e, acc = expression acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
     { eq_desc = Ematch { m with e; handlers } }, acc
  | _ -> assert false
  
(** Simplify a local declaration *)
and leq acc ({ l_eq } as l) =
  let l_eq, acc = equation acc l_eq in
  { l with l_eq }, acc

and default_opt f acc d =
  match d with
  | Init(e) -> let e, acc = f acc e in Init(e), acc
  | Else(e) -> let e, acc = f acc e in Else(e), acc
  | NoDefault -> NoDefault, acc

(** Equations **)
and equation acc ({ eq_desc } as eq) = 
  match eq_desc with
  | EQeq(p, e) ->
     let p, acc = pattern acc p in
     let e, acc = expression acc e in
     { eq with eq_desc = EQeq(p, e) }, acc
  | EQinit(x, e) ->
     let e, acc = expression acc e in
     let x, acc = rename acc x in
     { eq with eq_desc = EQinit(x, e) }, acc
  | EQemit(x, e_opt) ->
     let x, acc = rename acc x in
     let e_opt, acc =
       Util.optional_with_map expression acc e_opt in
     { eq_desc = EQemit(x, e_opt) }, acc
  | EQder { id; e; e_opt; handlers } ->
     let body acc ({ p_cond; p_body; p_env } as p_b) =
       let p_env, acc = build acc p_env in
       let p_cond, acc = scondpat acc p_cond in
       let p_body, acc = expression acc p_body in
       { p_b with p_cond; p_body }, acc in
     let id, acc = rename acc id in
     let e, acc = expression acc e in
     let e_opt, acc = Util.optional_with_map expression acc e_opt in
     let handlers, acc = Util.mapfold body acc handlers in
     { eq_desc = EQder { id; e; e_opt; handlers } }, acc
  | EQif { e; eq_true; eq_false } ->
     let e, acc = expression acc e in
     let eq_true, acc = equation acc eq_true in
     let eq_false, acc = equation acc eq_false in
     { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
  | EQmatch({ e; handlers } as m) ->
     let body acc ({ m_pat; m_body; m_env } as m_h) =
       let m_env, acc = build acc m_env in
       let m_pat, acc = pattern acc m_pat in
       let m_body, acc = equation acc m_body in
       { m_h with m_pat; m_body; m_env }, acc in
     let e, acc = expression acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
     { eq_desc = EQmatch { m with e; handlers } }, acc
  | EQlocal(eq_b) ->
     let eq_b, acc = block acc eq_b in
     { eq_desc = EQblock(eq_b) }, acc
  | EQand(eq_list) ->
     let eq_list, acc = Util.mapfold equation acc eq_list in
     { eq_desc = EQand(eq_list) }, acc
  | EQpresent({ handlers; default_opt } as h) ->
     let body acc ({ p_cond; p_body; p_env } as p_b) =
       let p_env, acc = build acc p_env in
       let p_cond, acc = scondpat acc p_cond in
       let p_body, acc = equation acc p_body in
       { p_b with p_cond; p_body }, acc in
     let handlers, acc =
       Util.mapfold body acc handlers in
     let default_opt, acc = default_opt acc default_opt in
     { eq_desc = EQpresent { h with handlers; default_opt } }, acc
  | EQautomaton({ handlers; state_opt } as a) ->
     let handler acc ({ s_state; s_let; s_body; s_trans } as h) =
       let s_state, acc = statepat acc s_state in
       let s_let, acc = slet acc s_let in
       let s_body, acc = block acc s_body in
       let s_trans, acc = Util.mapfold escape acc s_trans in
       { h with s_state; s_let; s_body; s_trans } in
     let state_opt, acc = state acc state_opt in
     let handlers, acc = Util.mapfold handler acc handlers in
     { eq with eq_desc = EQautomaton({ a with handlers; state_opt }) }, acc
  | EQempty -> eq, acc
  | EQassert(e) ->
     let e, acc = expression acc e in
     { eq with eq_desc = EQassert(e) }, acc
  | EQforloop({ for_size; for_kind; for_index; for_input; for_body } as f) ->
     let for_kind_t acc for_kind =
       match for_kind with
       | Kforeach -> Kforeach, acc
       | Kforward(for_exit_opt) ->
           let for_exit_opt, acc = 
             Util.optional_with_map for_exit acc for_exit_opt in
           Kforward(for_exit_opt), acc in
     let body 
         acc ({ for_size; for_kind; for_index; for_input; for_body } as f) =
       let for_size, acc = Util.optional_with_map acc for_size in
       let for_kind, acc = for_kind_t acc for_kind in
       let for_index, acc = build acc for_index{for_size : 'size option;
    for_kind : 'info for_kind;
    for_index : Ident.t option;
    for_input : 'info for_input_desc localized list;
    for_body : 'body;
    for_resume : bool; 
  | _ -> assert false
     
and scondpat acc ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     let scpat1, acc = scondpat acc scpat1 in
     let scpat2, acc = scondpat acc scpat2 in
     { scpat with desc = Econdand(scpat1, scpat2) }, acc
  | Econdor(scpat1, scpat2) ->
     let scpat1, acc = scondpat acc scpat1 in
     let scpat2, acc = scondpat acc scpat2 in
     { scpat with desc = Econdor(scpat1, scpat2) }, acc
  | Econdexp(e) ->
     let e, acc = expression acc fun_defs e in
     { scpat with desc = Econdexp(e) }, acc
  | Econdpat(e, p) ->
     let e, acc = expression acc fun_defs e in
     let p, acc = pattern acc p in
     { scpat with desc = Econdpat(e, p) }, acc
  | Econdon(scpat, e) ->
     let scpat, acc = scondpat acc scpat in
     let e, acc = expression acc e in
     { scpat with desc = Econdon(scpat, e) }, acc

and vardec renaming ({ vardec_name = n } as v) =
    { v with vardec_name = rename n renaming }
  
and block acc ({ b_vars; b_body; b_env } as b) =
  let b_env, acc = build acc n_env in
  let n_list, acc = 
    Util.mapfold vardec acc b_vars in
  let b_body, acc = equation acc b_body in
  { b with b_vars; b_body; b_env }, acc

(** Convert a value into an expression. **)
let exp_of_value v =
  match v with
  | Vint(v) -> Econst(Eint(v))
  | Vbool(v) -> Econst(Ebool(v))
  | Vfloat(v) -> Econst(Efloat(v))
  | Vchar(v) -> Econst(Echar(v))
  | Vstring(v) -> Econst(Estring(v))
  | Vvoid -> Econst(Evoid)
  | Vconstr0 lname -> Econstr0 { lname }
  | Vconstr1(lname, v_list) -> 
     Econstr1 { lname; arg_list = exp_of_value v_list }
  | Vrecord(r_list) ->
  | Vpresent(v) ->
  | Vabsent(v) ->
  | Vstuple(v_list) ->
  | Vtuple(v_list) ->
  | Vstate0(id) ->
  | Vstate1(id, v_list) ->
  | Varray(a) ->
  | Vfun(f) ->
  | Vclosure { c_funexp; c_genv; c_env } ->
  | Vsizefun { s_params; s_body; s_genv; s_env } ->
  | Vsizefix : { bound; name; defs } ->
                     } -> pvalue
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
