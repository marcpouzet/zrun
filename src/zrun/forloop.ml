(***********************************************************************)
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

(* The evaluation functions for for loops. *)

open Error
open Monad
open Result
open Ident
open Genv
open Value
open Find
open Primitives
open Match

let (let+) v f =
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) -> f v

let (and+) v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(v1, v2)

(* index in a loop body *)
type index =
  (* [xi in e by e'] means that in the i-th iteration, xi = e.(e' * i) *)
  | Vinput : { ve : pvalue array; by : int option } -> index
  (* [j in e0 to e1 or j in e0 downto e1] means that in the i-th iteration *)
  (* j = i + e0 in the first case; j = e1 - i in the second with i in [0..n-1] *)
  | Vindex : { ve_left : int; ve_right : int; dir : bool } -> index


(* given an index environment [i_env = [x1\v1,...,xk\vk]]
 *- and index [i: [0..n-1]], returns an environment [l_env]
 *- where:
 *-  - if i_env(x) = Vinput { ve; by } then l_env(x) = ve.(by * i)
 *-  - if i_env(x) = Vindex { ve_left; ve_right; dir } then
                               l_env(x) = ve_left + i  if dir
                               l_env(x) = ve_right -i  otherwise *)
let geti loc v i =
  match v with
  | Vflat(v) ->
     let n = Array.length v in
     if (i < n) && (i >= 0) then return (Value(v.(i)))
     else error { kind = Earray_size { size = n; index = i }; loc }
  | Vmap { m_length; m_u } ->
     if (i < m_length) && (i >= 0) then
       let* v = m_u i in return (Value(v))
     else error { kind = Earray_size { size = m_length; index = i }; loc }

let geti_env loc i_env i =
  let s_env = Env.to_seq i_env in
  let entry v = { cur = v; last = None; default = None } in
  Result.seqfold
    (fun acc (x, v) ->
      match v with
      | Vindex { ve_left; ve_right; dir } ->
         let i = if dir then ve_left + i else ve_left - i in
         return (Env.add x (entry (Value(Vint(i)))) acc)
      | Vinput { ve; by } ->
         let i = match by with
           | None -> i | Some(v) -> i + v in
         let* vi = geti loc ve i in
         return (Env.add x (entry vi) acc))
    Env.empty s_env

(* [x_to_last_x local_env acc_env] returns [acc_env'] where *)
(* [Dom(acc_env) = Dom(acc_env')] and *)
(* [acc_env'(x) = { cur = bot; last = v }] if [local_env(x) = v] *)
let x_to_lastx local_env acc_env =
  Debug.print_ienv "x_to_last_x: local_env:" local_env;
  Debug.print_ienv "x_to_last_x (before): acc_env:" acc_env;
  let acc_env =
    Env.mapi
    (fun x entry ->
      let v = Find.find_value_opt x local_env in
      { entry with cur = Vbot; last = v })
    acc_env in
  Debug.print_ienv "x_to_last_x (after): acc_env" acc_env; acc_env

(* copy [last x] into [x] *)
let lastx_to_x acc_env =
  Env.mapi
    (fun x ({ last } as entry) -> 
       let v = match last with | None -> Vbot | Some(v) -> v in
       { entry with last = None; cur = v }) acc_env

(* given [x] and [env_list], returns array [v] st [v.(i) = env_list.(i).(x)] *)
(* when [missing <> 0] complete with a default element *)
let array_of missing loc (var_name, var_init, var_default) acc_env env_list =
  let* v_list =
    map
      (fun env ->
        find_value_opt var_name env |>
          Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc })
      env_list in
  (* if one is bot or nil, the result is bot or nil *)
  let v_list = Primitives.slist v_list in
  if missing = 0 then
    return (Primitives.lift (fun v -> Varray(Vflat(Array.of_list v))) v_list)
  else
    let* default =
      match var_init, var_default with
      | None, None ->
         let size = List.length env_list + missing in
         error { kind = Earray_cannot_be_filled { name = var_name;
                                                  size = size; missing };
                 loc }
      | _, Some _ ->
         find_default_opt var_name acc_env |>
           Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc }
      | Some _, None ->
         find_last_opt var_name acc_env |>
           Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc } in
    match default with
    | Vbot -> return Vbot
    | Vnil -> return Vnil
    | Value(d) ->
       let d_list = Util.list_of missing d in
       return (Primitives.lift
                 (fun v -> Varray(Vflat(Array.of_list (v @ d_list)))) v_list)

(* check that [v] is indeed an array of length [for_size] *)
let input loc v by =
  let+ v = v in
  match v with
  | Varray(a) ->
     let actual_size = Primitives.length a in
     return (Value(actual_size, Vinput { ve = a; by }))
  | _ -> error { kind = Etype; loc }

let index loc ve_left ve_right dir =
  let+ ve_left = ve_left and+ ve_right = ve_right in
  match ve_left, ve_right with
  | Vint(ve_left), Vint(ve_right) ->
     let actual_size =
       (if dir then ve_right - ve_left else ve_left - ve_right) + 1 in
     return (Value(actual_size, Vindex { ve_left; ve_right; dir }))
  | _ -> error { kind = Etype; loc }

(* loop iteration *)
(* parallel for loops; take a list of states *)
let foreach_i : (int -> 's -> ('r * 's, 'error) Result.t) -> 's list
                -> ('r list * 's list, 'error) Result.t =
  fun f s_list ->
  let rec for_rec i s_list =
    match s_list with
    | [] -> return ([], [])
    | s :: s_list ->
       let* x, s = f i s in
       let* x_list, s_list = for_rec (i+1) s_list in
       return (x :: x_list, s :: s_list) in
  for_rec 0 s_list

(* the same parallel loop except that [f] takes also an accumulator *)
(* that is passed from iteration [i] to iteration [i+1] *)
let foreach_with_accumulation_i f acc_env0 s_list =
  let rec for_rec i acc_env s_list =
    match s_list with
    | [] -> return ([], acc_env, [])
    | s :: s_list ->
       let* f_env, acc_env, s = f i acc_env s in
       let* f_env_list, acc_env, s_list = for_rec (i+1) acc_env s_list in
       return (f_env :: f_env_list, acc_env, s :: s_list) in
  for_rec 0 acc_env0 s_list

(* instantaneous for loop; take a single state and iterate on it *)
let forward_i n default f s =
  let rec for_rec default i s =
    if i = n then return (default, s)
    else
      let* v, s = f i s in
      for_rec v (i+1) s in
  for_rec default 0 s

let forward_i_without_exit_condition:
      int -> (int -> ('c star ientry Env.t as 'a) -> 'b state ->
              ('a * 'a * 'b state, 'e) Result.t) -> 'a -> 'b state ->
      ('a list * 'a * 'b state, 'e) Result.t =
  fun n f acc_env0 s ->
  let rec for_rec i acc_env s =
    Debug.print_ienv "Debut iteration" acc_env;
    if i = n then return ([], acc_env, s)
    else
      let* f_env, acc_env, s = f i acc_env s in
      Debug.print_ienv "Env iteration" f_env;
      let* env_list, acc_env, s = for_rec (i+1) acc_env s in
      return (f_env :: env_list, acc_env, s) in
  for_rec 0 acc_env0 s

(* instantaneous for loops with an exit condition [cond] *)
(* this condition must be combinational *)
let forward_i_with_while_condition loc n write f exit_condition acc_env0 s =
  let rec for_rec : int -> ('c star ientry Env.t as 'a) -> 'b state ->
                    ('a list * 'a * 'b state, 'e) Result.t =
    fun i acc_env s ->
    if i = n then return ([], acc_env, s)
    else
      (* the unless condition only sees global values, input values and *)
      (* accumulated values *)
      let* v = exit_condition i acc_env in
      match v with
      | Vbot ->
         let f_env = bot_env write in return (Util.list_of n f_env, acc_env, s)
      | Vnil ->
         let f_env = nil_env write in return (Util.list_of n f_env, acc_env, s)
      | Value(v) ->
           let* b =
             Opt.to_result ~none:{ kind = Etype; loc = loc } (is_bool v) in
           if b then
             let* f_env, acc_env, s = f i acc_env s in
             let* env_list, acc_env, s = for_rec (i+1) acc_env s in
             return (f_env :: env_list, acc_env, s)
           else return ([], acc_env, s) in
  for_rec 0 acc_env0 s

(* instantaneous for loops with an exit condition [cond] *)
(* this condition must be combinational *)
let forward_i_with_unless_condition loc n write f cond acc_env0 s =
  forward_i_with_while_condition loc n write f 
    (fun i env -> (cond i env)) acc_env0 s

let forward_i_with_unless_condition loc n write f exit_condition acc_env0 s =
  let rec for_rec : int -> ('c star ientry Env.t as 'a) -> 'b state ->
                    ('a list * 'a * 'b state, 'e) Result.t =
    fun i acc_env s ->
    if i = n then return ([], acc_env, s)
    else
      (* the unless condition only sees global values, input values and *)
      (* accumulated values *)
      let* v = exit_condition i acc_env in
      match v with
      | Vbot ->
         let f_env = bot_env write in return (Util.list_of n f_env, acc_env, s)
      | Vnil ->
         let f_env = nil_env write in return (Util.list_of n f_env, acc_env, s)
      | Value(v) ->
           let* b =
             Opt.to_result ~none:{ kind = Etype; loc = loc } (is_bool v) in
           if Stdlib.not b then
             let* f_env, acc_env, s = f i acc_env s in
             let* env_list, acc_env, s = for_rec (i+1) acc_env s in
             return (f_env :: env_list, acc_env, s)
           else return ([], acc_env, s) in
  for_rec 0 acc_env0 s

let forward_i_with_until_condition loc n write f exit_condition acc_env0 s =
  let rec for_rec : int -> ('c star ientry Env.t as 'a) -> 'b state ->
                    ('a list * 'a * 'b state, 'e) Result.t =
    fun i acc_env s ->
    if i = n then return ([], acc_env, s)
    else
      let* f_env, next_acc_env, s = f i acc_env s in
      (* the until condition only sees global values, input values and *)
      (* local values *)
      (* if [acc_env(last x) = v], add it to [f_env] *)
      let* v = 
        let local_env = Fix.complete_with_default acc_env f_env in
        exit_condition i local_env in
      match v with
      | Vbot ->
         let f_env = bot_env write in 
         return (Util.list_of n f_env, next_acc_env, s)
      | Vnil ->
         let f_env = nil_env write in 
         return (Util.list_of n f_env, next_acc_env, s)
      | Value(v) ->
           let* b =
             Opt.to_result ~none:{ kind = Etype; loc = loc } (is_bool v) in
           if b then
            return ([], next_acc_env, s)
           else  
             let* env_list, acc_env, s = for_rec (i+1) next_acc_env s in
             return (f_env :: env_list, acc_env, s) in
  for_rec 0 acc_env0 s

(* main entry functions *)

(* parallel loop: the step function is iterated with different states;
 *- output is an array. *)
let foreach loc sbody env i_env s_list =
  let* ve_list, s_list =
    foreach_i
      (fun i se ->
        let* env_0 = geti_env loc i_env i in
        let env = Env.append env_0 env in
        sbody env se) s_list in
  let ve_list = Primitives.slist ve_list in
  return
    (Primitives.lift (fun v -> Varray(Vflat(Array.of_list v))) ve_list, s_list)


(* One step of the evaluation of the body of a loop *)
let step loc sbody env i_env i acc_env s =
  Debug.print_ienv "Forward: Env:" env;
  Debug.print_ienv "Forward: Env acc (before):" acc_env;
  let* env_0 = geti_env loc i_env i in
  let env = Env.append env_0 (Env.append acc_env env) in
  let* local_env, s = sbody env s in
  (* every entry [x\v] from [acc_env] becomes [x \ { cur = bot; last = v }] *)
  let acc_env = x_to_lastx local_env acc_env in
  Debug.print_ienv "Forward: Env acc (after):" acc_env;
  return (local_env, acc_env, s)

(* Parallel loop with accumulation *)
(* every step computes an environment. The output [v/x] at iteration [i] *)
(* becomes an input [v/last x] for iteration [i+1] *)
let foreach_with_accumulation_i loc sbody env i_env acc_env0 s_list =
  let* env_list, acc_env, s_list =
    foreach_with_accumulation_i (step loc sbody env i_env) acc_env0 s_list in
  return (env_list, acc_env0, s_list)

(* hyperserial loop: the step function is iterated on the very same state;
 *- output is the last value *)
let forward loc sbody env i_env n default s =
  forward_i n default
      (fun i se ->
        let* env_0 = geti_env loc i_env i in
        let env = Env.append env_0 env in
        sbody env se) s

let exit_condition loc cond i_env env i local_env =
  let* env_0 = geti_env loc i_env i in
  let env = Env.append env_0 (Env.append local_env env) in
  cond env
  
(* [i_env] is the environment for indexes; [acc_env_0] is the environment *)
(* for accumulated variables; [env] is the current environment *)
let forward_i_without_exit_condition loc sbody env i_env acc_env0 n s =
  forward_i_without_exit_condition n (step loc sbody env i_env) acc_env0 s

let forward_i_with_while_condition loc write sbody cond env i_env acc_env0 n s =
  (* the condition cannot depend on the current values defined *)
  (* the body of the loop; it can only depend on accumulated values *)
  forward_i_with_while_condition loc n write
    (step loc sbody env i_env)
    (exit_condition loc cond i_env env)
    acc_env0 s

let forward_i_with_unless_condition loc write sbody cond env i_env acc_env0 n s =
  forward_i_with_unless_condition loc n write
    (step loc sbody env i_env)
    (exit_condition loc cond i_env env)
    acc_env0 s

let forward_i_with_until_condition loc write sbody cond env i_env acc_env0 n s =
  (* the condition can depend on the current values defined *)
  (* the body of the loop *)
  forward_i_with_until_condition loc n write
    (step loc sbody env i_env)
    (exit_condition loc cond i_env env)
    acc_env0 s
