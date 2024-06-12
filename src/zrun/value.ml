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

(* Set of values *)
(* noinitialized and non causal values *)

(* an input entry in the environment *)
type 'a ientry = { cur: 'a; last : 'a option; default : 'a option }

type 'a result = ('a, Error.error) Result.t

type 'a star =
  | Vnil : 'a star (* non initialized value *)
  | Vbot : 'a star (* bottom value *)
  | Value : 'a -> 'a star (* value *)
  
type pvalue =
  | Vint : int -> pvalue
  | Vbool : bool -> pvalue
  | Vfloat : float -> pvalue
  | Vchar : char -> pvalue
  | Vstring : string -> pvalue
  | Vvoid : pvalue
  | Vconstr0 : Lident.t -> pvalue
  | Vconstr1 : Lident.t * pvalue list -> pvalue
  | Vrecord : pvalue Ast.record list -> pvalue
  | Vpresent : pvalue -> pvalue
  | Vabsent : pvalue
  | Vstuple : pvalue list -> pvalue
  | Vtuple : pvalue star list -> pvalue
  | Vstate0 : Ident.t -> pvalue
  | Vstate1 : Ident.t * pvalue list -> pvalue
  | Varray : pvalue array -> pvalue
  (* imported stateless functions; they must verify that *)
  (* f(atomic v) not= bot *)
  | Vfun : (pvalue -> pvalue option) -> pvalue
  | Vclosure : pvalue closure -> pvalue
  (* function parameterized by sizes *)
  | Vsizefun : pvalue sizefun -> pvalue
  (* a representation for mutually recursive functions over sizes *)
  (* f where rec [f1<s,...> = e1 and ... fk<s,...> = ek] *)
  | Vsizefix : 
      { bound: int list option; (* the maximum number of iterations *)
        name: Ident.t; (* name of the defined function *)
        defs: pvalue sizefun Ident.Env.t; (* the set of mutually recursive
                                                function definitions *) 
      } -> pvalue

and 'a array =
  | Vflat : 'a Array.t -> 'a array
  | Vmap : 'a map -> 'a array

(* bounded maps *)
(* [get x i = v if x.left <= i <= right then x i
                  else match otherwise with | None -> error 
                                            | Some(x) -> get x i *)
and 'a map =
  { m_length : int; m_u : int -> 'a result }
     
(* a size parameterized expression - f <n1,...,nk> = e *)
and 'a sizefun = 
  { s_params: Ident.t list; 
    s_body: Misc.no_info Ast.exp; 
    s_genv: 'a Genv.genv; 
    s_env: 'a star ientry Ident.Env.t }
                                   
(* a functional value - [fun|node] x1 ... xn -> e *)
and 'a closure =
  { c_funexp : Misc.no_info Ast.funexp;
    c_genv: 'a Genv.genv;
    c_env: 'a star ientry Ident.Env.t }
                                     
and 'a state =
  | Sbot : 'a state
  | Snil : 'a state
  | Sempty : 'a state
  | Sval : 'a star -> 'a state
  | Sstatic : 'a -> 'a state
  | Slist : 'a state list -> 'a state
  | Sopt : 'a star option -> 'a state
  | Sinstance : 'a instance -> 'a state
  | Scstate : { pos : 'a star; der : 'a star } -> 'a state 
  | Szstate : { zin : bool; zout : 'a star } -> 'a state
  | Shorizon : { zin : bool; horizon : float } -> 'a state
  | Speriod :
      { zin : bool; phase : float; period : float; horizon : float } -> 
      'a state
  (* environment of values *)
  | Senv : 'a star ientry Ident.Env.t -> 'a state

(* instance of a node *)
and 'a instance =
  { init : 'a state; (* current state *)
    step : 'a closure; (* step function *)
  }

(*
type ('a, 's) costream =
  | CoF : { init : 's;
            step : 's -> ('a * 's) option } ->
          ('a, 's) costream

type ('a, 'b, 's) node =
  | CoFun : ('a list -> 'b option) -> ('a, 'b, 's) node
  | CoNode : { init : 's;
               step : 's -> 'a list -> ('b * 's) option } -> ('a, 'b, 's) node
 *)
