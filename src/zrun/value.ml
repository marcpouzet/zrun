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
type 'a ientry =
  { cur: 'a option; (* the current value of [x] *)
    last : 'a option; (* the value of [last x] *)
    default : 'a option; (* the default value of [x] *)
    reinit : bool; (* [last x] is defined by an equation [init x = ...] *)
  }

type 'a result = ('a, Error.error) Result.t

type 'a star =
  | Vnil (* non initialized value *)
  | Vbot (* bottom value *)
  | Value of 'a (* value *)

type value = pvalue star

and pvalue =
  | Vint of int
  | Vbool of bool
  | Vfloat of float
  | Vchar of char
  | Vstring of string
  | Vvoid 
  | Vconstr0 of Lident.t
  | Vconstr1 of Lident.t * pvalue list
  | Vrecord of pvalue Zelus.record list
  | Vpresent of pvalue 
  | Vabsent 
  | Vstuple of pvalue list
  | Vtuple of pvalue star list
  | Vstate0 of Ident.t
  | Vstate1 of Ident.t * pvalue list
  | Varray of pvalue array
  (* imported stateless functions; they must verify that *)
  (* f(atomic v) not= bot *)
  | Vifun of (pvalue -> pvalue option)
  (* user defined functions and nodes *)
  | Vfun of vfun
  | Vnode of instance
  (* function parameterized by sizes *)
  | Vsizefun of sizefun
  (* mutually recursive definition of size functions *)
  | Vsizefix of
      { bound: int list option; (* the maximum number of iterations *)
        name: Ident.t; (* name of the defined function *)
        defs: sizefun Ident.Env.t;
        (* the set of mutually recursive function definitions *) 
      }

and 'a array =
  | Vflat of 'a Array.t
  | Vmap of 'a map

(* bounded maps *)
(* [get x i = v if x.left <= i <= right then x i
                  else match otherwise with | None -> error 
                                            | Some(x) -> get x i *)
and 'a map =
  { m_length : int; m_u : int -> 'a result }

and sizefun = { s_f: int list -> value result; }

and vfun = { f_arity: int; f : value list -> value result }

(* instance of a node *)
and instance =
  { tkind: Zelus.tkind; (* discrete only or discrete/continuous-time state *)
    arity: int;
    init : state; (* current state *)
    step : state -> value -> (value * state) result; (* step function *)
  }

and state =
  | Sbot 
  | Snil 
  | Sempty 
  | Sval of value
  | Sstatic of pvalue
  | Slist of state list
  | Sopt of value option
  | Sinstance of instance
  | Scstate of { pos : value; der : value }
  | Szstate of { zin : bool; zout : value }
  | Shorizon of { zin : bool; horizon : float }
  | Speriod of
      { zin : bool; phase : float; period : float; horizon : float }
  (* environment of values *)
  | Senv of value ientry Ident.Env.t

(*
  Intuition: an expression is interpreted as a value of type:

  type ('a, 's) costream =
  | CoF : { init : 's;
            step : 's -> ('a * 's) option } ->
          ('a, 's) costream

  A functional value, combinatorial or stateful is interpreted as a value of type:

  type ('a, 'b, 's) node =
  | CoFun : ('a list -> 'b option) -> ('a, 'b, 's) node
  | CoNode : { init : 's;
               step : 's -> 'a list -> ('b * 's) option } -> ('a, 'b, 's) node

  Here, the set of values contains all the possible value; those that are
  produced at every step and those that are produced only at "compile time"
  or "instancitation time". They could be separated into two distinct sets
*)
