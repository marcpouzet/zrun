(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zélus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* static inlining; warning: this step must be done after static reduction *)
(* all function call [inline f e1 ... en] is replaced by *)
(* [let x1 = e1 in ... let xn = en in
    local o do eq in o_res] *)
(* if [f = [fun|node] p1...pn returns o eq] *)

open Misc
open Ident
open Lident
open Ast
open Monad
open Opt
open Result

let expression funs acc ({ e_desc } as e) =
  raise Mapfold.Fallback
