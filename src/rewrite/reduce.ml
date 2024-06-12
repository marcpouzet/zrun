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
open Defnames

type error =
  | Eval of Error.error (* error during evaluation *)
  | NotStatic of Location.t
  | NotStaticExp of no_info exp
  | NotStaticEq of no_info eq

exception Reduce of error

(* Invariant: defined names in the four environment are pairwise distinct *)
(* this is ensured if this is the case in the source *)
(* this compiler pass ensures it too *)
type 'a env =
  { e_renaming: Ident.t Ident.Env.t; (* environment for renaming *)
    e_values: 'a Ident.Env.t;  (* environment of values *)
    e_globals: 'a Genv.genv;   (* global environment *)
    e_sizes: int Ident.Env.t; (* environment of sizes *)}

let empty genv =
  { e_renaming = Ident.Env.empty;
    e_values = Ident.Env.empty;
    e_globals = genv;
    e_sizes = Ident.Env.empty;
  }

let update acc genv env =
  { e_renaming = Ident.Env.empty; e_values = env;
    e_globals = genv; e_sizes = Ident.Env.empty }

(** Build a renaming from an environment *)
let build ({ e_renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, e_renaming = Env.fold buildrec env (Env.empty, e_renaming) in
  env, { acc with e_renaming }

let catch loc v =
  match v with | Ok(v) -> v | Error(error) -> raise (Reduce (Eval error))

let pvalue loc c_env =
  let add acc (x, { Value.cur = v }) =
    let* v = Primitives.pvalue v |>
               Opt.to_result ~none: { Error.kind = Etype; loc } in
    return (Env.add x v acc) in
  let c_env = Env.to_seq c_env in
  let c_env = seqfold add Env.empty c_env in
  catch loc c_env

let rename { e_renaming } n = Env.find n e_renaming

let rename_t ({ e_renaming } as acc) n = Env.find n e_renaming, acc

let write_t acc { dv; di; der } =
  let dv = S.map (rename acc) dv in
  let di = S.map (rename acc) di in
  let der = S.map (rename acc) der in
  { dv; di; der }, acc

let type_expression acc ty = ty, acc

(* size expressions *)
let size_e e_loc acc si =
  let rec size_e { desc } =
    match desc with
    | Sint(v) -> v
    | Sfrac { num; denom } ->
       let v = size_e num in v / denom
    | Sident(n) ->
       let v = 
         try Env.find n acc.e_sizes 
         with Not_found -> raise (Reduce(NotStatic e_loc)) in
       v
    | Splus(s1, s2) ->
       let v1 = size_e s1 in
       let v2 = size_e s2 in
       v1 + v2
    | Sminus(s1, s2) ->
       let v1 = size_e s1 in
       let v2 = size_e s2 in
       v1 - v2
    | Smult(s1, s2) ->
       let v1 = size_e s1 in
       let v2 = size_e s2 in
       v1 * v2 in
  size_e si

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
       let ty, acc = type_expression acc ty in
       Etypeconstraintpat(p1, ty), acc in
  { p with pat_desc }, acc

let pattern acc p = pattern rename_t acc p

let default_t f acc d =
  match d with
  | Init(e) -> let e, acc = f acc e in Init(e), acc
  | Else(e) -> let e, acc = f acc e in Else(e), acc
  | NoDefault -> NoDefault, acc

let for_exit_t expression acc ({ for_exit } as fe) =
  let for_exit, acc = expression acc for_exit in
  { fe with for_exit }, acc

let for_kind_t expression acc for_kind =
  match for_kind with
  | Kforeach -> Kforeach, acc
  | Kforward(for_exit_opt) ->
     let for_exit_opt, acc = 
       Util.optional_with_map (for_exit_t expression) acc for_exit_opt in
     Kforward(for_exit_opt), acc
    
let for_size_t expression acc e = expression acc e

let for_input_t expression acc ({ desc } as fi) =
  let desc, acc = match desc with
    | Einput {id; e; by } ->
       let id, acc = rename_t acc id in
       let e, acc = expression acc e in
       let by, acc = Util.optional_with_map expression acc by in
       Einput { id; e; by }, acc
    | Eindex ({ id; e_left; e_right } as ind) ->
       let id, acc = rename_t acc id in
       let e_left, acc = expression acc e_left in
       let e_right, acc = expression acc e_right in
       Eindex { ind with id; e_left; e_right }, acc in
  { fi with desc }, acc
     
(** Expressions **)
let rec expression acc ({ e_desc; e_loc } as e) =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e, acc
  | Evar(x) ->
     let x, acc = rename_t acc x in
     { e with e_desc = Evar(x) }, acc
  | Elast(x) ->
     let x, acc = rename_t acc x in
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
     let l, acc = leq_t acc l in
     let e_let, acc = expression acc e_let in
     { e with e_desc = Elet(l, e_let) }, acc
  | Elocal(eq_b, e) ->
     let eq_b, acc = block acc eq_b in
     let e, acc = expression acc e in
     { e with e_desc = Elocal(eq_b, e) }, acc
  | Epresent({ handlers; default_opt }) ->
     let body acc ({ p_cond; p_body; p_env } as p_b) =
       let p_env, acc = build acc p_env in
       let p_cond, acc = scondpat acc p_cond in
       let p_body, acc = expression acc p_body in
       { p_b with p_cond; p_body }, acc in
     let handlers, acc =
       Util.mapfold body acc handlers in
     let default_opt, acc = default_t expression acc default_opt in
     { e with e_desc = Epresent { handlers; default_opt } }, acc 
  | Ematch({ e; handlers } as m) ->
     let body acc ({ m_pat; m_body; m_env } as m_h) =
       let m_env, acc = build acc m_env in
       let m_pat, acc = pattern acc m_pat in
       let m_body, acc = expression acc m_body in
       { m_h with m_pat; m_body; m_env }, acc in
     let e, acc = expression acc e in
     let handlers, acc =
       Util.mapfold body acc handlers in
     { e with e_desc = Ematch { m with e; handlers } }, acc
  | Eassert e -> let e, acc = expression acc e in
                              { e with e_desc = Eassert(e) }, acc
  | Ereset(e_body, e_c) ->
     let e_body, acc = expression acc e_body in
     let e_c, acc = expression acc e_c in
     { e with e_desc = Ereset(e_body, e_c) }, acc
  | Esizeapp { f; size_list } -> 
     (* after this step, there should be no static expressions left *)
     let v = expression_e acc f in
     let size_list = List.map (size_e e_loc acc) size_list in
     let v = Coiteration.sizeapply e_loc v size_list in
     let v = catch e_loc v in
     exp_of_value e_loc acc v, acc
  | Efun f ->
     let f, acc = funexp acc f in
     { e with e_desc = Efun f }, acc
  | Eforloop
     ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
     let for_vardec_t acc ({ desc = { for_array; for_vardec } } as f) =
       let for_vardec, acc = vardec acc for_vardec in
       { f with desc = { for_array; for_vardec } }, acc in
     let for_exp_t acc for_exp =
       match for_exp with
       | Forexp { exp; default } ->
          let exp, acc = expression acc exp in
          let default, acc = Util.optional_with_map expression acc default in
          Forexp { exp; default }, acc
       | Forreturns { returns; body; r_env } ->
          let r_env, acc = build acc r_env in
          let returns, acc = Util.mapfold for_vardec_t acc returns in
          let body, acc = block acc body in
          Forreturns { returns; body; r_env }, acc in
     let for_env, acc = build acc for_env in
     let for_size, acc =
       Util.optional_with_map (for_size_t expression) acc for_size in
     let for_kind, acc = for_kind_t expression acc for_kind in
     let for_input, acc =
       Util.mapfold (for_input_t expression) acc for_input in
     let for_body, acc = for_exp_t acc for_body in
     { e with e_desc =
                Eforloop
                  { f with for_size; for_kind; for_index; for_input;
                           for_body; for_env } }, acc

and funexp acc ({ f_args; f_body; f_env } as f) =
  let f_env, acc = build acc f_env in
  let arg acc v_list = Util.mapfold vardec acc v_list in
  let f_args, acc = Util.mapfold arg acc f_args in
  let f_body, acc = result acc f_body in
  { f with f_args; f_body; f_env }, acc

(** Eval an expression *)
and expression_e acc e =
  let v = Coiteration.vexp acc.e_globals (Match.liftv acc.e_values) e in
  catch e.e_loc v

(** Try to evaluate and expression; expect the result to be boolean *)
and try_expression_bool acc e =
  let env = Match.liftv acc.e_values in
  (* let l = Env.to_list env in *)
  let v = 
    Coiteration.try_vexp_into_bool acc.e_globals env e in
  match v with
  | Ok(v) -> Some(v) | _ -> None

(** Equations **)
and equation acc ({ eq_desc; eq_write } as eq) = 
  let eq_write, acc = write_t acc eq_write in
  let eq, acc = match eq_desc with
    | EQeq(p, e) ->
       let p, acc = pattern acc p in
       let e, acc = expression acc e in
       { eq with eq_desc = EQeq(p, e) }, acc
    | EQinit(x, e) ->
       let e, acc = expression acc e in
       let x, acc = rename_t acc x in
       { eq with eq_desc = EQinit(x, e) }, acc
    | EQemit(x, e_opt) ->
       let x, acc = rename_t acc x in
       let e_opt, acc =
         Util.optional_with_map expression acc e_opt in
       { eq with eq_desc = EQemit(x, e_opt) }, acc
    | EQder { id; e; e_opt; handlers } ->
       let body acc ({ p_cond; p_body; p_env } as p_b) =
         let p_env, acc = build acc p_env in
         let p_cond, acc = scondpat acc p_cond in
         let p_body, acc = expression acc p_body in
         { p_b with p_cond; p_body }, acc in
       let id, acc = rename_t acc id in
       let e, acc = expression acc e in
       let e_opt, acc = Util.optional_with_map expression acc e_opt in
       let handlers, acc = Util.mapfold body acc handlers in
       { eq with eq_desc = EQder { id; e; e_opt; handlers } }, acc
    | EQif { e; eq_true; eq_false } ->
       (* two cases; either [e] is a compile-time boolean value or not *)
       let v = try_expression_bool acc e in
       let eq, acc = match v with 
         | None -> let e, ac = expression acc e in
                   let eq_true, acc = equation acc eq_true in
                   let eq_false, acc = equation acc eq_false in
                   { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
         | Some(b) ->
            if b then equation acc eq_true else equation acc eq_false in
       eq, acc
    | EQmatch({ e; handlers } as m) ->
       let body acc ({ m_pat; m_body; m_env } as m_h) =
         let m_env, acc = build acc m_env in
         let m_pat, acc = pattern acc m_pat in
         let m_body, acc = equation acc m_body in
         { m_h with m_pat; m_body; m_env }, acc in
       let e, acc = expression acc e in
       let handlers, acc =
         Util.mapfold body acc handlers in
       { eq with eq_desc = EQmatch { m with e; handlers } }, acc
    | EQlocal(eq_b) ->
       let eq_b, acc = block acc eq_b in
       { eq with eq_desc = EQlocal(eq_b) }, acc
    | EQand(eq_list) ->
       let eq_list, acc = Util.mapfold equation acc eq_list in
       { eq with eq_desc = EQand(eq_list) }, acc
    | EQpresent({ handlers; default_opt }) ->
       let body acc ({ p_cond; p_body; p_env } as p_b) =
         let p_env, acc = build acc p_env in
         let p_cond, acc = scondpat acc p_cond in
         let p_body, acc = equation acc p_body in
         { p_b with p_cond; p_body }, acc in
       let handlers, acc =
         Util.mapfold body acc handlers in
       let default_opt, acc = default_t equation acc default_opt in
       { eq with eq_desc = EQpresent { handlers; default_opt } }, acc
    | EQautomaton({ handlers; state_opt } as a) ->
       let statepat acc ({ desc } as spat) =
         let desc, acc = match desc with
           | Estate0pat(id) ->
              let id, acc = rename_t acc id in
            Estate0pat(id), acc
         | Estate1pat(id, id_list) ->
            let id, ac = rename_t acc id in
            let id_list, acc = Util.mapfold rename_t acc id_list in
            Estate1pat(id, id_list), acc in
         { spat with desc }, acc in
       let rec state acc ({ desc } as st) =
         let desc, acc  = match desc with
           | Estate0(id) ->
              let id, acc = rename_t acc id in
              Estate0(id), acc
           | Estate1(id, e_list) ->
              let id, acc = rename_t acc id in
              let e_list, acc = Util.mapfold expression acc e_list in
              Estate1(id, e_list), acc
           | Estateif(e, st1, st2) ->
              let e, acc = expression acc e in
              let st1, acc = state acc st1 in
              let st2, acc = state acc st2 in
              Estateif(e, st1, st2), acc in
         { st with desc }, acc in
       let escape acc ({ e_cond; e_let; e_body; e_next_state; e_env } as esc) =
         let e_env, acc = build acc e_env in
         let e_cond, acc = scondpat acc e_cond in
         let e_let, acc = slet acc e_let in
         let e_body, acc = block acc e_body in
         let e_next_state, acc = state acc e_next_state in
         { esc with e_cond; e_let; e_body; e_next_state; e_env }, acc in
       let handler acc ({ s_state; s_let; s_body; s_trans } as h) =
         let s_state, acc = statepat acc s_state in
         let s_let, acc = slet acc s_let in
         let s_body, acc = block acc s_body in
         let s_trans, acc = Util.mapfold escape acc s_trans in
         { h with s_state; s_let; s_body; s_trans }, acc in
       let state_opt, acc = Util.optional_with_map state acc state_opt in
       let handlers, acc = Util.mapfold handler acc handlers in
       { eq with eq_desc = EQautomaton({ a with handlers; state_opt }) }, acc
    | EQempty -> eq, acc
    | EQassert(e) ->
       let e, acc = expression acc e in
       { eq with eq_desc = EQassert(e) }, acc
    | EQforloop
       ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
       let for_eq_t acc { for_out; for_block } =
         let for_out_t acc
               ({ desc = { for_name; for_out_name; for_init; for_default } } as f) =
           let for_name, acc = rename_t acc for_name in
           let for_out_name, acc = 
             Util.optional_with_map rename_t acc for_out_name in
           let for_init, acc = Util.optional_with_map expression acc for_init in
           let for_default, acc =
             Util.optional_with_map expression acc for_default in
           { f with desc = { for_name; for_out_name; for_init; for_default } },
           acc in
         let for_out, acc =
           Util.mapfold for_out_t acc for_out in
         let for_block, acc = block acc for_block in
         { for_out; for_block }, acc in
       let for_env, acc = build acc for_env in
       let for_size, acc =
         Util.optional_with_map (for_size_t expression) acc for_size in
       let for_kind, acc = for_kind_t expression acc for_kind in
       let for_input, acc =
         Util.mapfold (for_input_t expression) acc for_input in
       let for_body, acc = for_eq_t acc for_body in
       { eq with eq_desc =
                   EQforloop
                     { f with for_size; for_kind; for_index; for_input;
                              for_body; for_env } }, acc
    | EQreset(eq, e_c) ->
       let eq, acc = equation acc eq in
       let e_c, acc = expression acc e_c in
       { eq with eq_desc = EQreset(eq, e_c) }, acc
    | EQlet(leq, eq) ->
       let leq, acc = leq_t acc leq in
       let eq, acc = equation acc eq in
       { eq with eq_desc = EQlet(leq, eq) }, acc
    | EQsizefun ({ sf_id; sf_id_list; sf_e; sf_env } as sf) ->
       let sf_env, acc = build acc sf_env in
       let sf_id, acc = rename_t acc sf_id in
       let sf_id_list, acc = Util.mapfold rename_t acc sf_id_list in
       let sf_e, acc = expression acc sf_e in
       { eq with eq_desc = 
                   EQsizefun { sf with sf_id; sf_id_list; sf_e; sf_env } },
       acc in
  { eq with eq_write }, acc

and slet acc leq_list = Util.mapfold leq_t acc leq_list

(* eval a definition *)
and leq_e acc leq =
  let l_env =
    Coiteration.vleq acc.e_globals (Match.liftv acc.e_values) leq in
  match l_env with
  | Ok(l_env) -> l_env | Error(error) -> raise (Reduce (Eval error))

and leq_t acc ({ l_kind; l_eq; l_env } as leq) =
  let l_env, acc = build acc l_env in
  let l_eq, acc = equation acc l_eq in
  let acc = match l_kind with
    | Kconst | Kstatic ->
       (* static evaluation *)
       let l_env = leq_e acc leq in
       { acc with e_values = Env.append l_env acc.e_values }
    | Kany -> acc in
  { leq with l_eq; l_env }, acc

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
     let e, acc = expression acc e in
     { scpat with desc = Econdexp(e) }, acc
  | Econdpat(e, p) ->
     let e, acc = expression acc e in
     let p, acc = pattern acc p in
     { scpat with desc = Econdpat(e, p) }, acc
  | Econdon(scpat, e) ->
     let scpat, acc = scondpat acc scpat in
     let e, acc = expression acc e in
     { scpat with desc = Econdon(scpat, e) }, acc

and vardec acc ({ var_name; var_default; var_init; var_typeconstraint } as v) =
  let var_name, acc = rename_t acc var_name in
  let var_default, acc =
    Util.optional_with_map expression acc var_default in
  let var_init, acc = Util.optional_with_map expression acc var_init in
  let var_typeconstraint, acc = type_expression acc var_typeconstraint in
  { v with var_name; var_default; var_init; var_typeconstraint }, acc

                 
and block acc ({ b_vars; b_body; b_env; b_write } as b) =
  let b_env, acc = build acc b_env in
  let b_vars, acc = 
    Util.mapfold vardec acc b_vars in
  let b_body, acc = equation acc b_body in
  let b_write, acc = write_t acc b_write in
  { b with b_vars; b_body; b_env; b_write }, acc

and result acc ({ r_desc } as r) =
  let r_desc, acc = match r_desc with
    | Exp(e) -> let e, acc = expression acc e in Exp(e), acc
    | Returns(b_eq) -> let b_eq, acc = block acc b_eq in Returns(b_eq), acc in
  { r with r_desc }, acc


(** Convert a value into an expression. **)
and exp_of_value loc acc v =
  let rec exp_of_value acc v =
    let open Value in
    let e_desc = match v with
      | Vint(v) -> Econst(Eint(v))
      | Vbool(v) -> Econst(Ebool(v))
      | Vfloat(v) -> Econst(Efloat(v))
      | Vchar(v) -> Econst(Echar(v))
      | Vstring(v) -> Econst(Estring(v))
      | Vvoid -> Econst(Evoid)
      | Vconstr0 lname -> Econstr0 { lname }
      | Vconstr1(lname, v_list) -> 
         Econstr1 { lname; arg_list = List.map (exp_of_value acc) v_list }
      | Vrecord(r_list) ->
         let r_list =
           List.map (fun { label; arg } -> { label; arg = exp_of_value acc arg })
             r_list in
         Erecord r_list
      | Vstuple(v_list) ->
         Etuple (List.map (exp_of_value acc) v_list)
      | Vtuple(v_list) ->
         let exp_of_value acc v = 
           match v with 
             Vbot | Vnil -> raise (Reduce(NotStatic loc)) 
             | Value(v) -> exp_of_value acc v in
         let e_list = List.map (exp_of_value acc) v_list in
         Etuple(e_list)
      | Vpresent _ | Vabsent | Vstate0 _ | Vstate1 _ ->
         (* no such values should be produced statically *)
         assert false
      | Varray _ -> assert false
      | Vfun _  -> assert false
      | Vclosure { c_funexp; c_genv; c_env } ->
         (* Warning: add part of [g_env and c_env] in acc *)
         let c_env = pvalue loc c_env in
         let acc = update acc c_genv c_env in
         let f, _ = funexp acc c_funexp in Efun f
      | Vsizefun _ | Vsizefix _ -> 
         (* there should be no static computation anymore *)
         assert false in
    { e_desc; e_loc = Location.no_location; e_info = no_info } in
  exp_of_value acc v

(* The main function. Reduce every definition *)
let implementation acc ({ desc } as impl) =
  let desc, acc = match desc with
    | Eopen _ -> desc, acc
    | Eletdecl { d_names; d_leq } ->
       let d_leq, acc = leq_t acc d_leq in
       Eletdecl { d_names; d_leq }, acc
    | Etypedecl _ -> desc, acc in
  { impl with desc }, acc

let set_index_t n = Ident.set n
let get_index_t () = Ident.get ()

let program genv { p_impl_list; p_index } =
  try
    set_index_t p_index;
    let p_impl_list, acc = 
      Util.mapfold implementation (empty genv) p_impl_list in
    let p_index = get_index_t () in
    { p_impl_list; p_index }
  with
  | Reduce(error) ->
     match error with
     | Eval { kind; loc } -> Error.message loc kind; raise Error
     | NotStatic(loc) ->
        Format.eprintf
          "@[%aInternal error (static reduction):@,\
           the expression to be reduced is not static.@.@]"
        Location.output_location loc;
        raise Error
     | NotStaticExp(e) ->
        Format.eprintf
          "@[%aInternal error (static reduction):@,\
           static evaluation failed because the expression is not static.@.@]"
          Printer.expression e;
        raise Error
     | NotStaticEq(eq) ->
        Format.eprintf
          "@[%aInternal error (static reduction):@,\
           static evaluation failed because the equation is not static.@.@]"
          Printer.equation eq;
        raise Error
