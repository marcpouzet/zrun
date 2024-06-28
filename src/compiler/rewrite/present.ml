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

(* removing present statements *)
open Misc
open Location
open Ident
open Zelus
open Aux
open Mapfold

(* compilation of signal pattern matching                               *)
(* present                                                              *)
(*   | x1(p1) & ... & -> do ... done                                    *)
(*   | x2(p2) & x1(p3) & ...                                            *)
(*   end                                                                *)
(*                                                                      *)
(*   - rewrite the pattern matching such a signal name is assigned to   *)
(*   a column. Boolean conditions are put in an extra column.           *)
(*                                                                      *)
(*   present                                                            *)
(*   | x1(p1) & ... & cond1 -> do ... done                              *)
(*   | x1(p3) & ... & cond2 -> ...                                      *)
(*   end                                                                *)
(*                                                                      *)
(*   - then produce a regular pattern matching construct                *)
(*     every handler is marked to be activated on an event              *)
(*                                                                      *)
(*   match x1, ... cond1, ..., condn with                               *)
(*   | Present(p1), ..., true, ... -> (* zero = true *) ...             *)
(*   | Present(p3), ..., _,  true -> (* zero = true *) ...              *)
(*   end                                                                *)
(* the bit [zero] indicates that the branch corresponds to a *)
(* zero-crossing. It is set to [true] only when the context is continuous *)
(*                                                                      *)
(*                                                                      *)
(* a signal x is represented by a pair (bit, value)                     *)


(** representation of signals *)
(* a [signal] is represented as an optional value *)
let present_name = Lident.Modname(Initial.stdlib_name "P")
let absent_name = Lident.Modname(Initial.stdlib_name "A")
let emit e = Aux.constr1 present_name [e]
let absent = Aux.constr0 absent_name

let presentpat pat = Aux.pmake (Econstr1pat(present_name, [pat]))

(* implementation of the presence test ? of a signal *)
(* match e with P _ -> true | A -> false *)
let test e =
  Eapp { is_inline = false;
         f = Aux.global_in_stdlib "snd"
               (maketype [e.e_typ] Initial.typ_bool),
                  [e])
    
let eq_match total e l = 
  let block_do_done =
    { b_vars = []; b_locals = []; b_body = []; b_loc = no_location;
      b_env = Env.empty; 
      b_write = Deftypes.empty } in
  (* if [total = false] complete with an empty block [do done] *)
  let l = if total then l
    else l @ [{ m_pat = { Zaux.wildpat with p_typ = e.e_typ };
                m_body = block_do_done; m_env = Env.empty;
		m_reset = false; m_zero = false }] in
  eqmake (EQmatch(ref true, e, l))

(* build the environment for signals from a typing environment *)
(* every signal [x: t sig] is associated to a pair [xv, xp] of two fresh *)
(* names. [xv: t] and [xp: bool] *)
let build signals l_env =
  let make n ({ t_typ = ty; t_sort = sort } as tentry)
	   (signals, n_list, new_env) = 
    match Ztypes.is_a_signal ty with
      | Some(ty) ->
	  let xv = Zident.fresh ((Zident.source n) ^ "v") in
	  let xp = Zident.fresh ((Zident.source n) ^ "p") in
	  let sort_v, sort_p =
	    match sort with
	    | Sstatic -> Sstatic, Sstatic
	    | Sval -> Sval, Sval
	    | Svar _
	    | Smem _ -> Deftypes.variable,
			Svar { v_combine = None;
			       v_default = Some(Cimmediate(Ebool(false))) } in
	  Env.add n (xv, xp, ty) signals,
	  (Zaux.vardec xv) :: (Zaux.vardec xp) :: n_list,
	  Env.add xv { t_typ = ty; t_sort = sort_v }
		  (Env.add xp { t_typ = typ_bool; t_sort = sort_p } new_env)
      | None ->
	signals, (Zaux.vardec_from_entry n tentry) :: n_list,
	Env.add n tentry new_env in
  Env.fold make l_env (signals, [], Env.empty)

(* equality between expressions. for efficiency purpose *)
(* we restrict to simple cases *)
let equal e1 e2 =
  match e1.e_desc, e2.e_desc with
    | Econst(i), Econst(j) when (i = j) -> true
    | Elocal(i), Elocal(j) when (i = j) -> true
    | Elast(i), Elast(j) when (i = j) -> true
    | _ -> false

(* the member function *)
let mem e exps = List.exists (equal e) exps

(* rename written variables [w] according to a substitution [signals] *)
(* the field [w.dr] is not concerned *)
let defnames signals ({ dv = dv; di = di } as w) =
  let defname n acc = 
    try let nv, np, _ = Env.find n signals in S.add nv (S.add np acc)
    with Not_found -> S.add n acc in
  { w with dv = S.fold defname dv S.empty; di = S.fold defname di S.empty }

(* separate signal testing from boolean condition in a signal pattern *)
let split spat =
  let rec split (se_list, pat_list, cond_list) spat =
    match spat.desc with
      | Econdand(sp1, sp2) | Econdor(sp1, sp2) ->
          split (split (se_list, pat_list, cond_list) sp2) sp1
      | Econdexp(e) ->
          se_list, pat_list, e :: cond_list
      | Econdon(sp1, e) ->
	  let se_list, pat_list, cond_list = 
	    split (se_list, pat_list, cond_list) sp1 in
	  se_list, pat_list, e :: cond_list
      | Econdpat(e, pat) ->
          e :: se_list, pat :: pat_list, cond_list in
  split ([], [], []) spat

and equation signals eq_list eq =
  match eq.eq_desc with
  | EQpresent(present_handler_list, b_opt) ->
      present_handlers signals eq_list present_handler_list b_opt
  | _ -> raise Mapfold.Fallback

and expression signals e =
  match e.e_desc with
  | Epresent(present_handler_list, b_opt) ->
     present_handler signals eq_list present_handler_list b_opt
  | _ -> raise Mapfold.Fallback

and match_handler signals ({ m_body = b } as handler) =
  let _, b = block signals b in { handler with m_body = b }

(* Translating a present statement *)
(* a present statement is translated into a pattern-matching statement *)
(* [is_cont = true] means that the present constructs run in a continuous context *)
and present_handlers signals eq_list handler_list b_opt =
  (* compute the set of expressions from a signal pattern matching *)
  (* expressions appearing more than once are shared *)
  let rec unique exps spat =
    match spat.desc with
      | Econdand(spat1, spat2) | Econdor(spat1, spat2) -> 
	  unique (unique exps spat1) spat2
      | Econdexp(e) | Econdpat(e, _) ->
          if mem e exps then exps
          else e :: exps
      | Econdon(spat1, e) ->
          unique (if mem e exps then exps else e :: exps) spat1 in

  let unique handler_list =
    List.fold_left
      (fun exps { p_cond = spat } -> unique exps spat) [] handler_list in

  (* normalize a signal pattern *)
  let rec norm spat acc =
    match spat.desc with
      | Econdor(spat1, spat2) -> norm spat1 (norm spat2 acc)
      | Econdpat _ | Econdexp _ | Econdand _ | Econdon _ -> spat :: acc in

  (* find the pattern associated to a signal in a signal pattern *)
  let pat spat se cont =
    let rec patrec spat =
      match spat.desc with
        | Econdand(spat1, spat2) ->
            begin try patrec spat1 with Not_found -> patrec spat2 end
        | Econdpat(e, pat) when (equal e se) || (e == se) -> presentpat pat
        | Econdexp(e) when (equal e se) || (e == se) -> truepat
        | Econdon(_, e) when (equal e se) || (e == se) -> truepat
	| Econdon(spat1, _) -> patrec spat1
	| _ -> raise Not_found in
    try
      (patrec spat) :: cont
    with
      Not_found ->
        { Zaux.wildpat with p_typ = se.e_typ } :: cont in

  (* build the pattern *)
  let pattern exps { p_cond = spat; p_body = b; p_env = h0 } =
    let pattern spat =
      let pat_list = List.fold_right (pat spat) exps [] in
      match pat_list with
	| [] -> assert false
	| [pat] -> pat
	| _ -> tuplepat(pat_list) in
    (* extract the list of simple signals patterns without "|" (or) *)
    let spat_list = norm spat [] in
    let pat_list = List.map pattern spat_list in
    let pat = orpat pat_list in
    (* the flag [zero] is true when [is_cont] is true *)
    let _, b = block signals b in
    { m_pat = pat; m_body = b; m_env = h0; 
      m_reset = false; m_zero = true } in
    
  (* first build the two association tables *)
  let exps = unique handler_list in
  (* compile each of them *)
  (* produces the expression to match *)
  let e = match exps with 
    | [e] -> exp signals e | _ -> tuple (List.map (exp signals) exps) in
  (* produces the handlers *)
  let pat_block_list = List.map (pattern exps) handler_list in
  (* treat the optional default handler *)
  let total, pat_block_list =
    match b_opt with
    | None -> false, pat_block_list
    | Some(b) ->
       let _, b = block signals b in
       true, pat_block_list @ 
	       [{ m_pat = { Zaux.wildpat with p_typ = e.e_typ }; m_body = b; 
		  m_env = Env.empty; m_reset = false; m_zero = false }] in
  (eq_match total e pat_block_list) :: eq_list

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; global_funs } in
  let { p_impl_list } as p, acc = Mapfold.program_it funs [] p in
  { p with p_impl_list = acc @ p_impl_list }

