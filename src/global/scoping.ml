(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2023 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* rewrite the parging tree into an ast *)
(* that is, change [id: String.t] into [id: Ident.t] *)

open Parsetree
open Ident

module Error =
  struct
    type error =
      | Evar of string
      | Enon_linear_pat of string
      | Enon_linear_record of string
      | Enon_linear_automaton of string
      | Enon_linear_forloop of string
      | Eautomaton_with_mixed_transitions
      | Emissing_in_orpat of string
                           
    exception Err of Location.t * error
                     
    let error loc kind = raise (Err(loc, kind))
                       
    let message loc kind =
      begin match kind with
      | Evar(name) ->
         Format.eprintf "%aScoping error: The value identifier %s is unbound.@."
           Location.output_location loc name
      | Enon_linear_pat(name) ->
          Format.eprintf "%aScoping error: The variable %s is bound several \
                     times in this pattern.@."
            Location.output_location loc name
      | Enon_linear_record(name) ->
         Format.eprintf
           "%aScoping error: The label %s is defined several times.@."
            Location.output_location loc name
      | Emissing_in_orpat(name) ->
          Format.eprintf
            "%aScoping error: The variable %s must occur on both sides of \
               this pattern.@."
            Location.output_location loc name
      | Enon_linear_automaton(name) ->
          Format.eprintf
            "%aScoping error: the state %s is defined several times in \
               this automaton.@."
            Location.output_location loc name
      | Enon_linear_forloop(name) ->
          Format.eprintf
	    "%aScoping error: The variable %s is bound several times \
               in this loop.@."
            Location.output_location loc name
      | Eautomaton_with_mixed_transitions ->
	 Format.eprintf
	   "%aScoping error: this automaton mixes weak \
            and strong transitions.@."
	   Location.output_location loc
      end;
      raise Misc.Error 
end

module S = Set.Make (String)

module Env =
  struct
    include Map.Make(String)

    (* update an environment *)
    let append env0 env =
      fold (fun x v acc -> update x (function _ -> Some(v)) acc)
        env0 env

    (* makes a renaming for a set of names *)
    let make defnames env =
      S.fold (fun s acc -> let m = fresh s in add s m acc) defnames env
  end


(* make a block *)
let make_block loc s_vars s_eq =
  { Ast.b_vars = s_vars; Ast.b_body = s_eq;
    Ast.b_loc = loc; Ast.b_write = Defnames.empty }

let name loc env n =
  try
    Env.find n env
  with
  | Not_found -> Error.error loc (Error.Evar(n))

let shortname = function | Name(n) -> n | Modname({ id }) -> id
                                                            
let longname ln =
  match ln with
  | Name(s) -> Lident.Name(s)
  | Modname { qual; id } ->
     Lident.Modname { Lident.qual = qual; Lident.id = id }

           
let vkind =
  function
  | Kconst -> Ast.Kconst
  | Kstatic -> Ast.Kstatic
  | Kany -> Ast.Kany

let tkind =
  function
  | Kdiscrete -> Ast.Kdiscrete | Khybrid -> Ast.Khybrid

let kind =
  function
  | Kfun(v) -> Ast.Kfun(vkind v)
  | Knode(t) -> Ast.Knode(tkind t)

let immediate c =
  match c with
  | Eint(i) -> Ast.Eint(i)
  | Ebool(b) -> Ast.Ebool(b)
  | Efloat(f) -> Ast.Efloat(f)
  | Evoid -> Ast.Evoid
  | Estring(s) -> Ast.Estring(s)
  | Echar(c) -> Ast.Echar(c)
                
(* synchronous operators *)
let rec operator op =
  match op with
  | Efby -> Ast.Efby
  | Eifthenelse -> Ast.Eifthenelse
  | Eminusgreater -> Ast.Eminusgreater
  | Eunarypre -> Ast.Eunarypre
  | Eseq -> Ast.Eseq
  | Erun(i) -> Ast.Erun(i)
  | Eatomic -> Ast.Eatomic  
  | Etest -> Ast.Etest
  | Eup -> Ast.Eup
  | Edisc -> Ast.Edisc
  | Eperiod -> Ast.Eperiod
  | Ehorizon -> Ast.Ehorizon
  | Earray(op) -> Ast.Earray(array_operator op)

and array_operator op =
  match op with
  | Eget -> Ast.Eget
  | Eupdate -> Ast.Eupdate
  | Eget_with_default -> Ast.Eget_with_default
  | Eslice -> Ast.Eslice
  | Econcat -> Ast.Econcat
  | Earray_list -> Ast.Earray_list
  | Etranspose -> Ast.Etranspose
  | Ereverse -> Ast.Ereverse
  | Eflatten -> Ast.Eflatten
 
(* translate types. *)
let rec types { desc; loc } =
  let desc = match desc with
    | Etypevar(n) -> Ast.Etypevar(n)
    | Etypetuple(ty_list) -> Ast.Etypetuple(List.map types ty_list)
    | Etypeconstr(lname, ty_list) ->
       Ast.Etypeconstr(longname lname, List.map types ty_list)
    | Etypefun(k, ty_arg, ty_res) ->
       let ty_arg = types ty_arg in
       let ty_res = types ty_res in
       Ast.Etypefun(kind k, ty_arg, ty_res) in
  { Ast.desc = desc; Ast.loc = loc }

(** Build a renaming environment **)
(* if [check_linear = true], stop when the same name appears twice *)
let buildpat check_linear defnames p =
  let rec build acc { desc } =
    match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> acc
    | Econstr1pat(_, p_list) | Etuplepat(p_list) ->
        build_list acc p_list
    | Evarpat(n) ->
	if S.mem n acc then 
        if check_linear 
        then Error.error p.loc (Error.Enon_linear_pat(n)) else acc
        else S.add n acc
    | Ealiaspat(p, n) ->
	let acc = build acc p in S.add n acc
    | Eorpat(p1, p2) -> 
	let orpat loc acc0 acc1 acc =
        let one key acc =
          if S.mem key acc1 then
            if S.mem key acc then
	      if check_linear 
              then Error.error loc (Error.Enon_linear_pat(key)) else acc
	      else S.add key acc
          else
	    Error.error loc (Error.Emissing_in_orpat(key)) in
        S.fold one acc0 acc in
        let acc1 = build S.empty p1 in
        let acc2 = build S.empty p2 in
        let acc = orpat p.loc acc1 acc2 acc in acc
    | Etypeconstraintpat(p, ty) -> build acc p
    | Erecordpat(l_p_list) -> build_record_list p.loc acc l_p_list
	
  and build_record_list loc acc label_pat_list =
    let rec buildrec acc labels label_pat_list =
      match label_pat_list with
      | [] -> acc
      | (lname, pat_label) :: label_pat_list ->
	  (* checks that the label appears only once *)
          let label = shortname lname in
          if S.mem label labels
          then Error.error loc (Error.Enon_linear_record(label))
          else
            buildrec (build acc pat_label) (S.add label labels)
              label_pat_list in
    buildrec acc S.empty label_pat_list
  and build_list acc p_list = 
    List.fold_left build acc p_list in
  build defnames p

(* compute the set of names defined by an equation *)
let rec buildeq defnames { desc } =
  match desc with
  | EQeq(pat, _) -> buildpat false defnames pat
  | EQder(x, _, _, _) | EQinit(x, _) | EQemit(x, _) -> S.add x defnames
  | EQreset(eq, _) -> buildeq defnames eq
  | EQand(and_eq_list) ->
     List.fold_left buildeq defnames and_eq_list
  | EQlocal(v_list, eq) ->
     let defnames_v_list = List.fold_left build_vardec S.empty v_list in
     let defnames_eq = buildeq S.empty eq in
     S.union defnames (S.diff defnames_eq defnames_v_list)
  | EQlet(_, eq) -> buildeq defnames eq
  | EQif(_, eq1, eq2) ->
     let defnames = buildeq defnames eq1 in
     buildeq defnames eq2
  | EQmatch(_, h_list) ->
     List.fold_left build_match_handler defnames h_list
  | EQpresent(p_h_list, b_opt) ->
     let defnames = 
       List.fold_left build_present_handler defnames p_h_list in
     let defnames =
       match b_opt with
       | NoDefault -> defnames
       | Init(eq) | Else(eq) -> buildeq defnames eq in
     defnames
  | EQautomaton(a_h_list, _) ->
     List.fold_left build_automaton_handler defnames a_h_list
  | EQempty ->  defnames
  | EQassert _ -> defnames
  | EQforloop({ for_body }) -> build_for_body_eq defnames for_body
    
and build_vardec defnames { desc = { var_name }; loc } =
  if S.mem var_name defnames then Error.error loc (Enon_linear_pat(var_name));
  S.add var_name defnames

and build_for_vardec defnames { desc = { for_vardec } } =
  build_vardec defnames for_vardec

and build_match_handler defnames { desc = { m_body } } =
  buildeq defnames m_body

and build_present_handler defnames { desc = { p_body } } =
  buildeq defnames p_body
  
and build_state_name acc { desc; loc } =
  match desc with
  | Estate0pat(n) | Estate1pat(n, _) ->
     if Env.mem n acc then Error.error loc (Error.Enon_linear_automaton(n));
     let m = fresh n in
     Env.add n m acc

and build_block defnames { desc = { b_vars; b_body }; loc } =
  let bounded_names = List.fold_left build_vardec S.empty b_vars in
  let defnames_body = buildeq S.empty b_body in
  bounded_names, S.union defnames (S.diff defnames_body bounded_names)
  
and build_automaton_handler defnames
  { desc = { s_body; s_until; s_unless } } =
  let bounded_names, defnames_s_body = build_block S.empty s_body in
  let defnames_s_trans =
    List.fold_left build_escape defnames_s_body s_until in
  let defnames_s_trans =
    List.fold_left build_escape defnames_s_trans s_unless in
  S.union defnames (S.diff defnames_s_trans bounded_names)

and build_escape defnames { desc = { e_body } } =
  let _, defnames_e_body = build_block S.empty e_body in
  S.union defnames defnames_e_body

and build_for_body_eq defnames { for_out; for_block } =
  (* [xi [init e] [default e]] means that [xi] is defined by the for loop *)
  (* and visible outside of it. On the contrary *)
  (* [xi [init e] [default e] out x] means that [xi] stay local and *)
  (* [x] is defined by the for loop and visible outside of it *)
  let build_for_out (acc_left, acc_right) { desc = { for_name; for_out_name } } =
    match for_out_name with
    | None -> acc_left, acc_right
    | Some(x) -> S.add for_name acc_left, S.add x acc_right in
  let acc_left, acc_right =
    List.fold_left build_for_out (S.empty, S.empty) for_out in
   
 (* computes defnames for the block *)
  let _, defnames_body = build_block defnames for_block in
  S.union defnames
    (S.union (* remove [xi] in defnames *)
       (S.diff defnames_body acc_left) acc_right)
        
let buildeq eq =
  let defnames = buildeq S.empty eq in
  Env.make defnames Env.empty
  
(** Patterns **)
let rec pattern_translate env { desc; loc } =
  let desc = match desc with
    | Ewildpat -> Ast.Ewildpat
    | Econstpat(im) -> Ast.Econstpat(immediate im)
    | Econstr0pat(ln) -> Ast.Econstr0pat(longname ln)
    | Econstr1pat(ln, p_list) ->
       Ast.Econstr1pat(longname ln, pattern_translate_list env p_list)
    | Etuplepat(p_list) -> Ast.Etuplepat(pattern_translate_list env p_list)
    | Evarpat(n) -> Ast.Evarpat(name loc env n)
    | Ealiaspat(p, n) ->
       Ast.Ealiaspat(pattern_translate env p, name loc env n)
    | Eorpat(p1, p2) ->
       Ast.Eorpat(pattern_translate env p1, pattern_translate env p2)
    | Etypeconstraintpat(p, ty) ->
       Ast.Etypeconstraintpat(pattern_translate env p, types ty)
    | Erecordpat(l_p_list) ->
       Ast.Erecordpat
         (List.map (fun (lname, p) -> { Ast.label = longname lname;
                                        Ast.arg = pattern_translate env p })
	    l_p_list) in
  { Ast.pat_desc = desc; Ast.pat_loc = loc }
  
and pattern_translate_list env p_list = List.map (pattern_translate env) p_list

(* Build the renaming environment then translate *)
and pattern env p =
  let defnames = buildpat true S.empty p in
  let env0 = Env.make defnames Env.empty in
  pattern_translate env0 p, env0

let present_handler scondpat body env { desc = { p_cond; p_body }; loc } =
  let scpat, env_scpat = scondpat env p_cond in
  let env = Env.append env_scpat env in
  let p_body = body env p_body in
  { Ast.p_cond = scpat; Ast.p_body = p_body; Ast.p_loc = loc }

let match_handler body env { desc = { m_pat; m_body }; loc } = 
  let m_pat, env_m_pat = pattern env m_pat in
  let env = Env.append env_m_pat env in
  let m_body = body env m_body in
  { Ast.m_pat = m_pat; Ast.m_body = m_body; Ast.m_loc = loc;
    Ast.m_reset = false; Ast.m_zero = false }

(* [env_pat] is the environment for names that appear on the *)
(* left of a definition. [env] is for names that appear on the right *)
let rec equation env_pat env { desc; loc } =
  let eq_desc =
    match desc with
    | EQeq(pat, e) ->
       let pat = pattern_translate env_pat pat in
       let e = expression env e in
       Ast.EQeq(pat, e)
    | EQder(x, e, e0_opt, p_h_list) ->
       Ast.EQder(name loc env x, expression env e,
                   Util.optional_map (expression env) e0_opt,
                   List.map
                     (present_handler scondpat expression env) p_h_list)
    | EQinit(x, e) -> EQinit(name loc env x, expression env e)
    | EQemit(x, e_opt) ->
       EQemit(name loc env x, Util.optional_map (expression env) e_opt)
    | EQreset(eq, e) ->
       let eq = equation env_pat env eq in
       let e = expression env e in
       Ast.EQreset(eq, e)
    | EQand(and_eq_list) ->
       let and_eq_list = List.map (equation env_pat env) and_eq_list in
       Ast.EQand(and_eq_list)
    | EQlocal(v_list, eq) ->
       let v_list, env_v_list = vardec_list env v_list in
       let env_pat = Env.append env_v_list env_pat in
       let env = Env.append env_v_list env in
       let eq = equation env_pat env eq in
       Ast.EQlocal(make_block loc v_list eq)
    | EQlet(l_eq, in_eq) ->
       let l_eq, env = letin env l_eq in
       let in_eq = equation env_pat env in_eq in
       Ast.EQlet(l_eq, in_eq)
    | EQif(e, eq1, eq2) ->
       let e = expression env e in
       let eq1 = equation env_pat env eq1 in
       let eq2 = equation env_pat env eq2 in
       Ast.EQif(e, eq1, eq2)
    | EQmatch(e, m_h_list) ->
       let e = expression env e in
       let m_h_list =
         List.map (match_handler (equation env_pat) env) m_h_list in
       Ast.EQmatch { is_total = false; e; handlers = m_h_list }
    | EQautomaton(a_h_list, st_opt) ->
       let is_weak, is_strong =
         List.fold_left
           (fun (is_weak, is_strong)
	        { desc = { s_until; s_unless } } ->
	     is_weak || (s_until <> []), is_strong || (s_unless <> []))
           (false, false) a_h_list in
       if is_weak && is_strong
       then Error.error loc (Error.Eautomaton_with_mixed_transitions)
       else
         let env_for_states =
           (* build the association table for state names *)
           List.fold_left
             (fun acc { desc = { s_state } } -> build_state_name acc s_state)
             Env.empty a_h_list in
         let handlers =
           List.map
             (automaton_handler is_weak env_for_states env_pat env) a_h_list in
         let state_opt =
           Util.optional_map (state env_for_states env) st_opt in
         Ast.EQautomaton({ is_weak; handlers; state_opt })
    | EQempty ->
       Ast. EQempty
    | EQassert(e) -> Ast.EQassert(expression env e)
    | EQpresent(p_h_list, eq_opt) ->
       let handlers =
         List.map (present_handler scondpat (equation env_pat) env) p_h_list in
       let default_opt =
         match eq_opt with
         | NoDefault -> Ast.NoDefault
         | Init(eq) -> Ast.Init(equation env_pat env eq)
         | Else(eq) -> Ast.Else(equation env_pat env eq) in
       Ast.EQpresent({ handlers; default_opt })
    | EQforloop(f) ->
       Ast.EQforloop(forloop_eq env_pat env f)
  in
  (* set the names defined in the equation *)
  { Ast.eq_desc = eq_desc; Ast.eq_write = Defnames.empty;
    Ast.eq_loc = loc }

and trans_for_input env acc i_list =
  let input acc { desc; loc } =
    let desc, acc = match desc with
      | Einput { id; e; by } ->
         if Env.mem id acc then Error.error loc (Error.Enon_linear_forloop(id))
         else
           let m = fresh id in
           let e = expression env e in
           let by = Util.optional_map (expression env) by in
           Ast.Einput { id = m; e; by }, Env.add id m acc
      | Eindex { id; e_left; e_right; dir } ->
         if Env.mem id acc then Error.error loc (Error.Enon_linear_forloop(id))
         else
           let m = fresh id in
           let e_left = expression env e_left in
           let e_right = expression env e_right in
           Ast.Eindex { id = m; e_left; e_right; dir }, Env.add id m acc in
    { Ast.desc = desc; Ast.loc = loc }, acc in
  Util.mapfold input acc i_list

and trans_for_out env i_env for_out =
  (* [local_out_env] is the environment for variables defined in the for loop *)
  (* that are associated to an output [xi out x]. In that case, [xi] is local *)
  (* to the loop body; [x] is the only visible defined variable *)
  (* otherwise, [xi] is defined by the for loop and visible outside of it *)
  let for_out_one local_out_env
        { desc = { for_name; for_init; for_default; for_out_name }; loc } =
    (* check that output name [xi] is distinct from input names. This is *)
    (* not mandatory but makes loops simpler to understand *)
    if Env.mem for_name i_env then Error.error loc (Enon_linear_pat(for_name));
    let for_name, local_out_env =
      match for_out_name with
      | None -> name loc env for_name, local_out_env
      | Some(x) -> let m = fresh for_name in
                   m, Env.add for_name m local_out_env in
    let for_init =
      Util.optional_map (expression env) for_init in
    let for_default =
      Util.optional_map (expression env) for_default in
    let for_out_name = Util.optional_map (name loc env) for_out_name in
    { Ast.desc =
        { Ast.for_name = for_name; Ast.for_init = for_init;
          Ast.for_default = for_default; Ast.for_out_name = for_out_name };
      Ast.loc = loc },
    local_out_env in
    Util.mapfold for_out_one Env.empty for_out

(* translation of for loops *)
and forloop_eq env_pat env { for_size; for_kind; for_index; for_input; for_resume;
                             for_body = { for_out; for_block } } =
    let for_size = Util.optional_map (expression env) for_size in
    let for_index, i_env =
      match for_index with
      | None -> None, Env.empty
      | Some(id) -> let m = fresh id in Some(m), Env.singleton id m in
    let for_input, i_env =
      trans_for_input env i_env for_input in
    let env = Env.append i_env env in
    let for_out, local_out_env =
      trans_for_out env i_env for_out in
    let env = Env.append local_out_env env in
    let env_pat = Env.append local_out_env env in
    let env_body, for_block = block equation env_pat env for_block in
    let for_kind =
      match for_kind with
      | Kforeach -> Ast.Kforeach
      | Kforward(e_opt) ->
         Ast.Kforward(Util.optional_map (expression env_body) e_opt) in
    { Ast.for_size = for_size;
      Ast.for_kind = for_kind;
      Ast.for_index = for_index;
      Ast.for_input = for_input;
      Ast.for_body = { for_out; for_block };
      Ast.for_resume = for_resume }

(** Translating a sequence of local declarations *)
and leqs env l = Util.mapfold letin env l

and letin env { desc = { l_kind; l_rec; l_eq }; loc } =
  let env_pat = buildeq l_eq in
  let new_env = Env.append env_pat env in
  let l_eq = equation env_pat (if l_rec then new_env else env) l_eq in
  let l_kind = vkind l_kind in
  { l_kind; l_rec; l_eq; l_loc = loc }, new_env
  
and vardec env
{ desc = { var_name; var_init; var_default;
           var_typeconstraint; var_clock; var_is_last }; loc } =
  let var_default =
    Util.optional_map (expression env) var_default in
  let var_init =
    Util.optional_map (expression env) var_init in
  let var_typeconstraint =
    Util.optional_map types var_typeconstraint in
  let m = name loc env var_name in
  { Ast.var_name = m; Ast.var_init = var_init;
    Ast.var_default = var_default;
    Ast.var_typeconstraint = var_typeconstraint;
    Ast.var_clock = var_clock; Ast.var_loc = loc;
    Ast.var_is_last = var_is_last }

(* treat a list of variable declarations *)
(*- computes the list of names;
 *- builds an initial environment;
 *- apply the substitution; 
 *- the two steps is necessary because 
 *- [local x init y, y init x do ... x = ... and y = ... done]
 *- is corrects and a short-cut for 
 *- [local last x, last y do last x = y and last y = x and ... done] *)
and vardec_list env v_list =
  let defnames = List.fold_left build_vardec S.empty v_list in
  let env_v_list = Env.make defnames Env.empty in
  let env = Env.append env_v_list env in
  let v_list = List.map (vardec env) v_list in
  v_list, env_v_list 
       
and for_vardec env { desc = { for_array; for_vardec }; loc } =
  let for_vardec = vardec env for_vardec in
  { Ast.desc = { Ast.for_array = for_array; Ast.for_vardec = for_vardec };
    Ast.loc = loc }

and for_vardec_list env for_v_list =
  let defnames = List.fold_left build_for_vardec S.empty for_v_list in
  let env_v_list = Env.make defnames Env.empty in
  let env = Env.append env_v_list env in
  let v_list = List.map (for_vardec env) for_v_list in
  v_list, env_v_list

(* [local x1 [init e1][default e'1],...,xn[...] do eq] *)
and block body env_pat env { desc = { b_vars; b_body }; loc } =
  let b_vars, env_b_vars = vardec_list env b_vars in
  let env_pat = Env.append env_b_vars env_pat in
  let env = Env.append env_b_vars env in
  let b = body env_pat env b_body in
  env, { Ast.b_vars = b_vars; Ast.b_body = b; Ast.b_loc = loc;
         Ast.b_write = Defnames.empty }
  
and state env_for_states env { desc; loc } =
  let desc = match desc with
    | Estate0(f) ->
       let f = try Env.find f env_for_states 
               with | Not_found -> Error.error loc (Error.Evar(f)) in
       Ast.Estate0(f)
    | Estate1(f, e_list) ->
       let f = try Env.find f env_for_states 
               with | Not_found -> Error.error loc (Error.Evar(f)) in
       let e_list = List.map (expression env) e_list in
       Ast.Estate1(f, e_list)
    | Estateif(e, se1, se2) ->
       Ast.Estateif(expression env e,
                      state env_for_states env se1,
                      state env_for_states env se2) in
  { Ast.desc = desc; Ast.loc = loc }
  
and statepat env_pat { desc; loc } =
  let desc, acc = match desc with
    | Estate0pat(f) ->
       let fm = try Env.find f env_pat
                with | Not_found -> Error.error loc (Error.Evar(f)) in
       Ast.Estate0pat(fm), Env.empty
    | Estate1pat(f, n_list) ->
       let fm = try Env.find f env_pat
                with | Not_found -> Error.error loc (Error.Evar(f)) in
       let n_list, acc =
         Util.mapfold
           (fun acc n -> let m = Ident.fresh n in m, Env.add n m acc)
           Env.empty n_list in
       Estate1pat(fm, n_list), acc in
  { Ast.desc = desc; Ast.loc = loc }, acc
  
  
and automaton_handler is_weak env_for_states env_pat env
{ desc = { s_state; s_let; s_body; s_until; s_unless }; loc } =
  let s_state, env_s_state = statepat env_for_states s_state in
  let env_pat = Env.append env_s_state env_pat in
  let env = Env.append env_s_state env in
  let s_let, env = leqs env s_let in
  let env, s_body = block equation env_pat env s_body in
  let s_trans =
    List.map (escape env_for_states env_pat env)
      (if is_weak then s_until else s_unless) in
  { Ast.s_state = s_state; Ast.s_let = s_let; Ast.s_body = s_body;
    Ast.s_trans = s_trans; Ast.s_loc = loc;
    Ast.s_reset = false }
  
and escape env_for_states env_pat env
{ desc = { e_reset; e_cond; e_let; e_body; e_next_state }; loc } = 
  let e_cond, env_e_cond  = scondpat env e_cond in
  let env_pat = Env.append env_e_cond env_pat in
  let env = Env.append env_e_cond env in
  let e_let, env = leqs env e_let in
  let env, e_body = block equation env_pat env e_body in
  let e_next_state = state env_for_states env e_next_state in
  { Ast.e_reset; Ast.e_cond = e_cond; Ast.e_let = e_let;
    Ast.e_body = e_body; Ast.e_next_state = e_next_state;
    Ast.e_loc = loc }
  
and scondpat env scpat =
  (* first build the set of names *)
  let rec build_scondpat acc { desc; loc } =
    match desc with
    | Econdand(scpat1, scpat2) ->
       build_scondpat (build_scondpat acc scpat1) scpat2
    | Econdor(scpat1, scpat2) ->
       let orcond loc acc0 acc1 acc =
         let one key acc =
           if S.mem key acc1 then
	     if S.mem key acc then
	       Error.error loc (Error.Enon_linear_pat(key))
	     else S.add key acc
           else
	     Error.error loc (Error.Emissing_in_orpat(key)) in
         S.fold one acc0 acc in
       let acc1 = build_scondpat S.empty scpat1 in
       let acc2 = build_scondpat S.empty scpat2 in
       let acc = orcond loc acc1 acc2 acc in
       acc
    | Econdexp _ -> acc
    | Econdpat(_, p) -> buildpat true acc p
    | Econdon(scpat, _) -> build_scondpat acc scpat in
  (* rename *)
  let scondpat env_scpat env scpat =
    let rec scondpat { desc; loc } =
      let desc = match desc with
	| Econdand(scpat1, scpat2) ->
	   Ast.Econdand(scondpat scpat1, scondpat scpat2)
	| Econdor(scpat1, scpat2) ->
	   Ast.Econdor(scondpat scpat1, scondpat scpat2)
	| Econdexp(e) ->
           Ast.Econdexp(expression env e)
	| Econdpat(e, p) ->
           Ast.Econdpat(expression env e, pattern_translate env_scpat p)
	| Econdon(scpat, e) ->
           Ast.Econdon(scondpat scpat, expression env e) in
      { Ast.desc = desc; Ast.loc = loc } in
    scondpat scpat in
  (* first build the environment for pattern variables *)
  let defnames = build_scondpat S.empty scpat in
  let env0 = Env.make defnames Env.empty in
  (* translate *)
  let scpat = scondpat env0 env scpat in
  scpat, env0
  
and expression env { desc; loc } =
  let desc =
    match desc with
    | Evar(Name(n)) ->
       begin try
           let m = Env.find n env in
           Ast.Elocal(m)
         with
         | Not_found ->
            Ast.Eglobal({ lname = Name(n) })
       end
    | Evar(Modname _ as ln) ->
       Ast.Eglobal({ lname = longname ln })
    | Econst(c) -> Ast.Econst(immediate c)
    | Econstr0(f) -> Ast.Econstr0 { lname = longname f }
    | Econstr1(f, e_list) ->
       Ast.Econstr1
         { lname = longname f; arg_list = List.map (expression env) e_list }
    | Elast(x) ->
       let x = try Env.find x env
               with | Not_found -> Error.error loc (Error.Evar(x)) in
       Ast.Elast(x)
    | Eop(op, e_list) ->
       let e_list = List.map (expression env) e_list in
       Ast.Eop(operator op, e_list)
    | Etuple(e_list) ->
       let e_list = List.map (expression env) e_list in
       Ast.Etuple(e_list)
    | Elet(leq, e) ->
       let leq, new_env = letin env leq in
       let e = expression new_env e in
       Ast.Elet(leq, e)
    | Eapp(f, arg_list) ->
       let f = expression env f in
       let arg_list = List.map (expression env) arg_list in
       Ast.Eapp(f, arg_list)
    | Erecord_access(e, lname) ->
       let e = expression env e in
       Ast.Erecord_access { arg = e; label = longname lname }
    | Erecord(label_e_list) ->
       Ast.Erecord(recordrec loc env label_e_list)
    | Erecord_with(e, label_e_list) ->
       Ast.Erecord_with(expression env e, recordrec loc env label_e_list)
    | Etypeconstraint(e, texp) ->
       Ast.Etypeconstraint(expression env e, types texp)
    | Efun(fd) -> Ast.Efun(funexp env fd)
    | Ematch(e, m_h_list) ->
       let e = expression env e in
       let m_h_list =
         List.map (match_handler expression env) m_h_list in
       Ast.Ematch { is_total = false; e; handlers = m_h_list }
    | Epresent(p_h_list, eq_opt) ->
       let handlers =
         List.map (present_handler scondpat expression env) p_h_list in
       let default_opt =
         match eq_opt with
         | NoDefault -> Ast.NoDefault
         | Init(e) -> Ast.Init(expression env e)
         | Else(e) -> Ast.Else(expression env e) in
       Ast.Epresent({ handlers; default_opt }) 
    | Ereset(e_body, e_res) ->
       Ast.Ereset(expression env e_body, expression env e_res)
    | Eassert(e_body) ->
       Ast.Eassert(expression env e_body)
    | Eforloop(f) ->
       Ast.Eforloop(forloop_exp env f)
  in
  { Ast.e_desc = desc; Ast.e_loc = loc }
  
and forloop_exp env 
    { for_size; for_kind; for_index; for_input; for_body; for_resume } =
  let for_size = Util.optional_map (expression env) for_size in
  let for_index, i_env =
      match for_index with
      | None -> None, Env.empty
      | Some(id) -> let m = fresh id in Some(m), Env.singleton id m in
  let for_input, i_env =
    trans_for_input env i_env for_input in
  let env = Env.append i_env env in
  let env_body, for_body = match for_body with
    | Forexp { exp; default } ->
       let exp = expression env exp in
       let default = Util.optional_map (expression env) default in
       env, Ast.Forexp { exp = exp; default = default }
    | Forreturns { returns; body } ->
       let returns, env_v_list = for_vardec_list env returns in
       let env = Env.append env_v_list env in
       let env_body, body = block equation env_v_list env body in
       env_body, Ast.Forreturns { returns; body } in
  let for_kind =
    match for_kind with
    | Kforeach -> Ast.Kforeach
    | Kforward(e_opt) ->
       Ast.Kforward(Util.optional_map (expression env_body) e_opt) in
  { Ast.for_size = for_size; Ast.for_kind = for_kind;
    Ast.for_index = for_index; Ast.for_input = for_input; Ast.for_body = for_body;
    Ast.for_resume = for_resume }
  
and recordrec loc env label_e_list =
  (* check that a label name appear only once *)
  let rec recordrec labels label_e_list =
    match label_e_list with
    | [] -> []
    | (lname, e) :: label_e_list ->
       (* check that labels are all different *)
       let l = shortname lname in
       if S.mem l labels
       then Error.error loc (Error.Enon_linear_record(l))
       else { Ast.label = longname lname; Ast.arg = expression env e } ::
              recordrec (S.add l labels) label_e_list in
  recordrec S.empty label_e_list
  
and funexp env { desc = { f_vkind; f_kind; f_atomic; f_args; f_body }; loc } =
  let f_args, env = Util.mapfold arg env f_args in
  let f_body = result env f_body in
  { Ast.f_vkind = vkind f_vkind;
    Ast.f_kind = kind f_kind; Ast.f_atomic = f_atomic;
    Ast.f_args = f_args; Ast.f_body = f_body; Ast.f_loc = loc }
  
and arg env v_list =
  let v_list, env_v_list = vardec_list env v_list in
  v_list, Env.append env_v_list env
                       
and result env { desc; loc } =
  let r_desc =
    match desc with
    | Exp(e) -> Ast.Exp(expression env e)
    | Returns(v_list, eq) ->
       let v_list, env_v_list = vardec_list env v_list in
       let env = Env.append env_v_list env in
       let eq = equation env_v_list env eq in
       Ast.Returns(make_block loc v_list eq) in
  { r_desc; r_loc = loc }
  
(* type declarations. *)
let rec type_decl { desc; loc } =
  let desc = match desc with
  | Eabstract_type -> Ast.Eabstract_type
  | Eabbrev(ty) -> Ast.Eabbrev(types ty)
  | Evariant_type(constr_decl_list) ->
      Ast.Evariant_type(List.map constr_decl constr_decl_list)
  | Erecord_type(n_ty_list) ->
      Ast.Erecord_type
        (List.map (fun (n, ty) -> (n, types ty)) n_ty_list) in
  { Ast.desc = desc; Ast.loc = loc }

and constr_decl { desc; loc } =
  let desc = match desc with
  | Econstr0decl(n) -> Ast.Econstr0decl(n)
  | Econstr1decl(n, ty_list) ->
      Ast.Econstr1decl(n, List.map types ty_list) in
  { Ast.desc = desc; Ast.loc = loc }

let type_decls n_params_typdecl_list =
  List.map (fun (n, pars, typdecl) -> (n, pars, type_decl typdecl))
    n_params_typdecl_list

let implementation { desc; loc } =
  try
    let desc = match desc with
      | Eopen(n) -> Ast.Eopen(n)
      | Eletdecl { name; const; e } ->
         let e = expression Env.empty e in
         Ast.Eletdecl { name = name; const = const; e = e}
      | Etypedecl { name; ty_params; size_params; ty_decl } ->
         let ty_decl = type_decl ty_decl in
         Ast.Etypedecl { name = name; ty_params; size_params; ty_decl } in
    { Ast.desc = desc; Ast.loc = loc }
  with
    Error.Err(loc, kind) -> Error.message loc kind
                          
let program i_list = List.map implementation i_list

let interface interf =
  try
    let desc = match interf.desc with
      | Einter_open(n) -> Ast.Einter_open(n)
      | Einter_typedecl { name; ty_params; size_params; ty_decl } ->
         let ty_decl = type_decl ty_decl in
         Ast.Einter_typedecl { name; ty_params; size_params; ty_decl }
      | Einter_constdecl { name; const; ty; info } ->
         let ty = types ty in
         Ast.Einter_constdecl { name; const = const; ty; info } in
      { Ast.desc = desc; Ast.loc = interf.loc }
  with
    | Error.Err(loc, err) -> Error.message loc err

let implementation_list = program
let interface_list inter_list = Util.iter interface inter_list
