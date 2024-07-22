(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Misc
open Zelus
open Value
open Ident
open Genv
open Find
open Monad
open Result
open Error

(* Computation of fixpoints *)
   
(* Dynamic check of causality. A set of equations is causal when all defined *)
(* variables are non bottom, provided free variables are non bottom *)
(* this a very strong constraint. In particular, it rejects the situation *)
(* of a variable that is bottom but not used. *)
(* causal(env)(env_out)(names) =
 *-               /\ (forall x in Dom(env), env(x) <> bot)
 *-               /\ (env_out, _ = fixpoint_eq genv sem eq n s_eq bot)
 *-               => (forall x in names /\ Dom(env_out), env_out(x) <> bot) *)
let causal loc
      (env: 'a star ientry Env.t) (env_out: 'a star ientry Env.t ) names =
  let bot v = match v with | Vbot -> true | _ -> false in
  let bot_option v = match v with | None -> false | Some(v) -> bot v in
  let bot_name n =
    let r = find_value_opt n env_out in
    match r with | None -> false | Some(v) -> bot v in
  let bot_names =
    if Env.for_all (fun _ { cur } -> not (bot_option cur)) env
    then S.filter bot_name names else S.empty in
  if !no_causality then return ()
  else 
    if S.is_empty bot_names then return ()
    else
      error { kind = Enot_causal(bot_names); loc = loc }

(* number of variables defined by an equation *)
(* it determines the number of iterations for the computation *)
(* of the least fixpoint *)
let size { eq_write = { Defnames.dv; Defnames.di } } =
  (* [der] names do not matter because their value is computed by the solver *)
  S.cardinal dv + S.cardinal di

(* return a default value. If [default] field is present, returns it *)
(* otherwise, returns the [last] field *)
let default_value last default =
  let open Opt in
  match last, default with
  | None, None -> none
  | (_, Some(v)) | (Some(v), None) -> return v
                                    
(* given an environment [env], a local environment [env_handler] *)
(* an a set of written variables [write] *)
(* [by env env_handler write] complete [env_handler] with entries in [env] *)
(* for variables that appear in [write] *)
(* this is used for giving the semantics of a control-structure, e.g.,: *)
(* [if e then do x = ... and y = ... else do x = ... done]. When [e = false] *)
(* the value of [y] is the default value given at the definition of [y] *)
(* If no default value is given (e.g., local x in ...), for the moment *)
(* we raise an error *)
let by loc env env_handler write =
  S.fold
    (fun x acc ->
      (* if [x in env] but not [x in env_handler] *)
      (* then either [x = last x] or [x = default(x)] depending *)
      (* on what is declared for [x]. *)
      let* { last; default } as entry =
        Env.find_opt x env |>
          Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = loc } in
      if Env.mem x env_handler then acc
      else
        let* acc = acc in
        let* v =
          default_value last default |>
            Opt.to_result ~none:{ kind = Eno_default(x); loc = loc } in
        return (Env.add x { entry with cur = Some(v) } acc))
    write (return env_handler) 
       
(* initialize [env_handler] with inputs from [write] *)
(* pre-condition: [Dom(env_handler) subseteq write] *)
let initialize env env_handler write =
  S.fold
    (fun x acc ->
      match Env.find_opt x env_handler with
      | Some(entry) -> Env.add x entry acc
      | None ->
         match Env.find_opt x env with
         | Some(entry) -> Env.add x entry acc
         | None -> acc (* this case should not arrive *))
    write Env.empty
  
(* given [env_in] and [env_out = [x1 \ { cur1 },..., xn \ { curn }] *)
(* returns [x1 \ { cur1; default x env; last1 },..., *)
(* xn \ { curn; default x env; lastn }]. [lasti] is the definition in *)
(* [env_out], if it exists; otherwise, it is that of [env_in] *)
let complete env_in env_out =
  let complete v v_in_env =
    match v, v_in_env with
    | None, _ -> v_in_env
    | Some _, _ -> v in
  Env.fold
    (fun x ({ cur; last } as entry) acc ->
      match Env.find_opt x env_in with
      | None -> Env.add x entry acc
      | Some { cur = cur_in_env; default; last = last_in_env } ->
         let cur = complete cur cur_in_env in
         let last = complete last last_in_env in
         Env.add x { entry with cur; last; default } acc)
    env_out Env.empty

(* equality of values in the fixpoint iteration. Because of monotonicity *)
(* only compare bot/nil with non bot/nil values. *)
let equal_values v1 v2 =
  match v1, v2 with
  | (Value _, Value _) | (Vbot, Vbot) | (Vnil, Vnil) -> true
  | _ -> false

(* bounded fixpoint combinator *)
(* computes a pre fixpoint f^n(bot) <= fix(f) *)
let fixpoint loc n stop f s bot =
  let rec fixpoint n v =
    if n <= 0 then (* this case should not happen *)
      error { kind = Efixpoint_limit; loc }
    else
      (* compute a fixpoint for the value [v] keeping the current state *)
      let* v', s' = f s v in
      if stop v v' then return (n, v', s') else fixpoint (n-1) v' in      
  (* computes the next state *)
  fixpoint n bot

(* Invariant: values in the environment are restricted by construction *)
(* to be either bot, nil or a primitive (atomic) value, i.e., a value *)
(* which is fully defined *)
(* stop the fixpoint when two successive environments are equal *)
let equal_env env1 env2 =
  let equal v1 v2 =
    match v1, v2 with
    | None, None -> true | Some(v1), Some(v2) -> equal_values v1 v2
    | _ -> false in
  Env.equal
    (fun { cur = cur1; last = last1; reinit = r1 }
         { cur = cur2; last = last2; reinit = r2 } ->
      (equal cur1 cur2) && (if r1 || r2 then equal last1 last2 else true))
    env1 env2

(* bounded fixpoint [n] for a set of mutually recursive equations *)
let eq genv env sem eq n s_eq bot =
  let sem s_eq env_in =
    Debug.print_ienv "Before step" env_in;
    let env = Env.append env_in env in
    let* env_out, s_eq = sem genv env eq s_eq in
    Debug.print_ienv "After step" env_out;
    let env_out = complete env_in env_out in
    return (env_out, s_eq) in
  let* m, env_out, s_eq = fixpoint eq.eq_loc n equal_env sem s_eq bot in
  return (env_out, s_eq)

(* fixpoint for mutually recursive definitions of size parameterized functions *)
(* [defs = [f1\Vsfun ...; fk\Vsfun ...]] *)
let sizefixpoint defs =
  Ident.Env.mapi 
    (fun f entry -> Match.entry (Vsizefix { bound = None; name = f; defs })) 
    defs
