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

(* type annotations for terms *)

type typinfo =
  { t_typ: Deftypes.typ;
    t_caus: Defcaus.tc;
    t_init: Definit.ti }

let no_info =
  { t_typ = Deftypes.no_typ;
    t_caus = Defcaus.no_typ;
    t_init = Definit.no_typ }
    
