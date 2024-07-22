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

(* Remove nested declaration of variables *)
(* Preserves the sequential order defined by let/in *)
(* declarations. If side-effects or unsafe functions appear, their *)
(* order given by the let/in is preserved *)
(* E.g., in [let x = e1 in e2], all side effects in [e1] are done before *)
(* those of [e2] *)
(* [let x = e1 in e2] has the behavior of [let x = e1 andthen y = e2 in y] *)

(* Invariant: an expression is normalized into a pair [(vardec, eq), e] *)
(* whose meaning is [local vardec do eq in e] *)
(* An equation is normalized into [local vardec do eq] *)

open Misc
open Location
open Ident
open Zelus
open Aux
open State
open Mapfold

let empty_eq = eqmake Defnames.empty EQempty
let empty_leq =
  { l_kind = Kstatic; l_rec = false; l_eq = empty_eq;
    l_loc = no_location; l_env = Env.empty }
let empty_block =
  { b_vars = []; b_body = empty_eq; 
    b_env = Env.empty; b_loc = no_location; b_write = Defnames.empty }

(* a structure to represent nested equations before they are turned into *)
(* Zelus equations *)
type 'a acc =
  { c_vardec: 'a exp vardec list State.t;
    c_eq: 'a eq State.t }

let empty = { c_vardec = State.Empty; c_eq = State.Empty }

let empty = { c_vardec = State.empty; c_eq = State.empty }
let par { c_vardec = v1; c_eq = c_eq1 } { c_vardec = v2; c_eq = c_eq2 } =
  { c_vardec = State.par v1 v2; c_eq = State.par c_eq1 c_eq2 }
let seq { c_vardec = v1; c_eq = c_eq1 } { c_vardec = v2; c_eq = c_eq2 } =
  { c_vardec = State.seq v1 v2; c_eq = State.seq c_eq1 c_eq2 }
let add_seq eq ({ c_eq } as ctx) =
  { ctx with c_eq = State.seq (State.singleton eq) c_eq }
let add_par eq ({ c_eq } as ctx) =
  { ctx with c_eq = State.par (State.singleton eq) c_eq }
let add_vardec vardec_list ({ c_vardec } as ctx) =
  { ctx with c_vardec = State.Cons(vardec_list, c_vardec) }
let add_names n_names ctx =
  let vardec_list = S.fold (fun id acc -> Aux.id_vardec id :: acc) n_names [] in
  add_vardec vardec_list ctx
				   				      
(* translate a context [acc] into an environment and an equation *)
let equations eqs =
  (* computes the set of sequential equations *)
  let rec seq eqs eq_list =
    match eqs with
    | State.Empty -> eq_list
    | State.Cons(eq, eqs) -> eq :: seq eqs eq_list
    | State.Seq(eqs1, eqs2) ->
       seq eqs1 (seq eqs2 eq_list)
    | State.Par(eqs1, eqs2) ->
       let par_eq_list = par [] eqs1 in
       let par_eq_list = par par_eq_list eqs2 in
       Aux.par par_eq_list :: eq_list
  (* and the set of parallel equations *)
  and par eq_list eqs =
    match eqs with
    | State.Empty -> eq_list
    | State.Cons(eq, eqs) -> par (eq :: eq_list) eqs
    | State.Seq(eqs1, eqs2) ->
       let seq_eq_list = seq eqs2 [] in
       let seq_eq_list = seq eqs1 seq_eq_list in
       Aux.seq seq_eq_list :: eq_list
    | State.Par(eqs1, eqs2) ->
       par (par eq_list eqs1) eqs2 in
  par [] eqs

(* build an equation [local vardec_list do eq done] from [acc] *)
let eq_local { c_vardec; c_eq } =
  let vardec_list = State.fold (@) c_vardec [] in
  let eq_list = equations c_eq in
  Aux.eq_local (block_make vardec_list eq_list)     

let e_local { c_vardec; c_eq } e =
  let vardec_list = State.fold (@) c_vardec [] in
  let eq_list = equations c_eq in
  Aux.e_local (block_make vardec_list eq_list) e    
  
let pattern funs acc p = p, acc

(* Translation of expressions *)
(* [expression funs { c_vardec; c_eq } e = [e', { c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq in e] and *)
(* [local c_vardec' do c_eq' in e'] are equivalent *)
let rec expression funs acc ({ e_desc } as e) =
  match e_desc with
  | Eop(Eseq, [e1; e2]) ->
     (* the sequential order is preserved *)
     (* [e1; e2] is a short-cut for [let _ = e1 in e2] *)
     let e1, acc_e1 = expression funs empty e1 in
     let e2, acc_e2 = expression funs empty e2 in
     e2, par acc (seq acc_e1 (add_seq (Aux.wildpat_eq e1) acc_e2))
  | Elet(l, e) ->
     (* the sequential order is preserved *)
     let _, acc_l = leq_t funs empty l in
     let e, acc_e = expression funs empty e in
     e, par acc (seq acc_l acc_e)
  | Elocal(b, e) ->
     (* the sequential order is preserved *)
     let _, acc_b = block funs empty b in
     let e, acc_e = expression funs empty e in
     e, par acc (seq acc_b acc_e)
  | _ -> Mapfold.expression funs acc e
     
(* Translate an equation. *)
(* [equation funs { c_vardec; c_eq } eq = empty_eq, [{ c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq and eq] and *)
(* [local c_vardec' do c_eq'] are equivalent *)
and equation funs acc ({ eq_desc } as eq) =
  let acc_eq = match eq_desc with 
    | EQand { eq_list } ->
       let _, acc = Util.mapfold (equation funs) empty eq_list in
       acc
    | EQinit(id, e_init) ->
       let e_init, acc_init = expression funs empty e_init in
       add_par { eq with eq_desc = EQinit(id, e_local acc_init e_init) } empty
    | EQlet(l, eq) ->
       (* the sequential order is preserved *)
       let _, acc_l = leq_t funs empty l in
       let eq, acc_eq = equation funs empty eq in
       seq acc_l acc_eq
    | EQlocal(b) ->
       let _, acc_b = block funs empty b in
       acc_b
    | _ ->
       let eq, acc = Mapfold.equation funs empty eq in
       seq acc (add_seq eq empty) in
  empty_eq, par acc acc_eq

and leq_t funs acc { l_eq = { eq_write } as l_eq } =
  let _, acc = equation funs acc l_eq in
  empty_leq, add_names (Defnames.names S.empty eq_write) acc

and move_init_into_equations acc ({ var_name; var_init } as v) =
  match var_init with
  | None -> v, acc
  | Some(e) ->
     { v with var_init = None; var_init_in_eq = true },
     par acc (add_seq (Aux.eq_init var_name e) empty)
     
and block funs acc { b_vars; b_body } =
  let b_vars, acc_b_vars =
    Util.mapfold (Mapfold.vardec funs) empty b_vars in
  let b_vars, acc_b_vars =
    Util.mapfold move_init_into_equations acc_b_vars b_vars in
  let _, acc_b_body = equation funs empty b_body in
  empty_block, (add_vardec b_vars (par acc (seq acc_b_vars acc_b_body)))

and if_eq funs acc (eq_true, eq_false) =
  let _, acc_true = equation funs empty eq_true in
  let _, acc_false = equation funs empty eq_false in
  (eq_local acc_true, eq_local acc_false), acc

and match_handler_eq funs acc ({ m_body } as m_h) =
  let _, acc_local = equation funs empty m_body in 
  { m_h with m_body = eq_local acc_local }, acc

and match_handler_e funs acc ({ m_body } as m_h) =
  let e, acc_local = expression funs empty m_body in 
  { m_h with m_body = e_local acc_local e }, acc

and present_handler_eq funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat funs acc p_cond in
  let _, acc_local = equation funs empty p_body in
  { p_b with p_cond; p_body = eq_local acc_local }, acc

and present_handler_e funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_cond, acc = Mapfold.scondpat funs acc p_cond in
  let p_body, acc_local = expression funs empty p_body in
  { p_b with p_cond; p_body = e_local acc_local p_body }, acc

and result funs acc ({ r_desc } as r) =
  let r_desc, acc = match r_desc with
  | Exp(e) ->
     let e, acc_local = expression funs empty e in
     Exp(e_local acc_local e), acc
  | Returns({ b_vars; b_body } as b) ->
     let b_vars, acc_b_vars =
       Util.mapfold (vardec funs) empty b_vars in
     let b_vars, acc_b_vars =
       Util.mapfold move_init_into_equations acc_b_vars b_vars in
     let _, acc_local = equation funs empty b_body in
     Returns({ b with b_vars; b_body = eq_local (seq acc_b_vars acc_local) }),
     acc in
  { r with r_desc }, acc

and letdecl funs acc (d_names, ({ l_eq } as leq)) =
  let _, acc_local = equation funs empty l_eq in
  (d_names, { leq with l_eq = eq_local acc_local }), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with pattern; expression; equation; leq_t; block;
                            if_eq; match_handler_eq; match_handler_e;
                            present_handler_eq; present_handler_e;
                            result; letdecl; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
