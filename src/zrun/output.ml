(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2026 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Format
open Lident
open Value

module Printer = Printer.Make(Noinfo)

let lident ff lid =
  match lid with
  | Name(s) -> fprintf ff "%s" s
  | Modname { qual; id } -> fprintf ff "%s.%s" qual id
                          
let print_list print po sep pf ff l =
  let rec printrec ff l =
    match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l -> printf "@[%a%s@ %a@]" print x sep printrec l in
  fprintf ff "@[%s%a%s@]" po printrec l pf

let rec pvalue ff v =
  match v with
  | Vint(i) -> fprintf ff "%i" i
  | Vbool(b) -> fprintf ff "%s" (if b then "true" else "false")
  | Vfloat(f) -> fprintf ff "%f" f
  | Vchar(c) -> fprintf ff "%c" c
  | Vstring(s) -> fprintf ff "%s" s
  | Vvoid -> fprintf ff "()"
  | Vtuple(l) ->
     print_list value "(" "," ")" ff l
  | Vstuple(l) ->
     print_list pvalue "(" "," ")" ff l
  | Vconstr0(lid) -> lident ff lid
  | Vconstr1(lid, l) ->
     fprintf ff "@[<hov1>%a%a@]" lident lid
       (print_list pvalue "(" "," ")") l 
  | Vstate0(id) -> Ident.fprint_t ff id
  | Vstate1(id, l) ->
     fprintf
       ff "@[<hov 1>%a(%a)@]" Ident.fprint_t id
       (print_list pvalue "(" "," ")")  l
  | Vifun _ ->
     fprintf ff "<fun>"
  | Vfun _ -> fprintf ff "<fun>"
  | Vnode { n_tkind } ->
     fprintf ff "<%s>" (Printer.tkind n_tkind)
  | Vsizefun _ ->
     fprintf ff "<sizefun>"
  | Vrecord(l) ->
     let one ff { Zelus.arg; Zelus.label } =
       fprintf ff "@[<hov2>%a =@ %a@]"
         pvalue arg Lident.fprint_t label in
     print_list one "{" ";" "}" ff l
  | Vabsent ->
     fprintf ff "abs"
  | Vpresent(v) ->
     fprintf ff "!%a" pvalue v
  | Varray(a) -> parray ff a

and parray ff a =
  match a with
  | Vflat(v) ->
     fprintf ff "@[<hov1>[|%a|]@]"
       (fun ff v ->
         Array.iter (fun x -> fprintf ff "%a;@," pvalue x) v)
       v
  | Vmap{ m_length; m_u } ->
      fprintf ff "@[<hov1>'[|%a|]@]"
        (fun ff v -> List.iter (fun x ->
          match x with
          | Ok(x) -> fprintf ff "%a;@," pvalue x
          | Error(_) -> fprintf ff "error;@,"
        ) v)
        (List.init m_length m_u)

and value ff v =
  match v with
  | Vnil -> fprintf ff "nil"
  | Vbot -> fprintf ff "bot"
  | Value(v) -> pvalue ff v                 
              
(* print a state *)
let rec pstate ff s =
  match s with
  | Sbot -> fprintf ff "bot"
  | Snil -> fprintf ff "nil"
  | Sempty -> fprintf ff "()"
  | Sval(v) -> value ff v
  | Sstatic(v) -> fprintf ff "@[(static %a)@]" pvalue v
  | Slist(s_list) ->
      print_list pstate "[" ";" "]" ff s_list
  | Sopt(None) -> 
     fprintf ff "none" | Sopt(Some(v)) -> fprintf ff "(some %a)" value v
  | Sinstance { n_init } ->
     fprintf ff "@[<hov2>(instance@ %a)@]" pstate n_init
  | Scstate { pos; der } -> 
     fprintf ff "@[{ pos = %a; der = %a }@]" value pos value der
  | Szstate { zin; zout } ->
     fprintf ff "@[{ zin = %b; zout = %a }@]" zin value zout
  | Shorizon { zin; horizon } -> 
     fprintf ff "@[{ zin = %b; zout = %f }@]" zin horizon
  | Speriod { phase; period } -> 
     fprintf ff "@[{ phase = %f; period = %f }@]" phase period
  | Senv _ -> fprintf ff "@[(env)@]"

let pstate ff s =
  fprintf ff "%a@." pstate s

let value_flush ff v =
  fprintf ff "%a@." value v
let pvalue_flush ff l = 
  fprintf ff "%a@." pvalue l
let letdecl ff n_v_list =
  let onedecl ff (name, v) =
    fprintf ff "@[<hov 2>val %s =@ %a@]@." name pvalue v in
  List.iter (onedecl ff) n_v_list

(* output values for plotting - use with gnuplot *)
(* for an output that is a tuple, remove the "(", ")" and "," *)
let value_list_flush ff v =
  let pvalue ff v =
    match v with
    | Vtuple(l) -> print_list value "" "" "" ff l
    | Vstuple(l) -> print_list pvalue "" "" "" ff l
    | _ -> pvalue ff v in
  match v with
  | Vnil -> fprintf ff "nil"
  | Vbot -> fprintf ff "bot"
  | Value(v) -> pvalue ff v
