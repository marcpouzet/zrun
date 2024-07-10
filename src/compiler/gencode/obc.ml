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

(* abstract syntax tree of the object code *)

open Location
open Misc
open Ident

type name = string

type 'a record = { mutable label: Lident.t; arg: 'a }

type ('pattern, 'body) match_handler =
  { m_pat : 'pattern;
    m_body: 'body;
  }

type immediate =
  | Eint of int
  | Eint32 of int
  | Ebool of bool
  | Efloat of float
  | Echar of char
  | Estring of string
  | Evoid
  | Eany
      
type pattern = 
  | Ewildpat
  | Etuplepat of pattern list
  | Evarpat of Ident.t
  | Econstpat of immediate
  | Ealiaspat of pattern * Ident.t
  | Econstr0pat of Lident.t
  | Econstr1pat of Lident.t * pattern list
  | Eorpat of pattern * pattern
  | Erecordpat of (Lident.t * pattern) list
  | Etypeconstraintpat of pattern * type_expression

(* a continuous state variable [x] is a pair *)
(* with two fields: [x.der] for its derivative. [x.pos] *)
(* for its current value. *)
(* a zero-crossing variable [x] has two field: [x.zin] is true when *)
(* the solver has detected a zero-crossing. [x.zout] is the value *)
(* to be observed for a zero-crossing *)

(* expressions are expected to be safe; unsafe ones must be put *)
(* into instructions *)
type exp = 
  | Econst: immediate -> exp (* immediate constant *)
  | Econstr0: Lident.t -> exp (* 0-ary and 1-ary constructor *)
  | Econstr1: Lident.t * exp list -> exp
  | Eglobal: Lident.t -> exp (* global variable *)
  | Elocal: Ident.t -> exp (* read of local value *)
  | Evar : { is_mutable: is_mutable; name: Ident.t } -> exp
  (* read of local variable *)
  | Estate_access : left_state_value -> exp (* read of a state variable *)
  | Eaccess : exp * exp -> exp  (* access in an array *)
  | Eupdate : size * exp * exp * exp -> exp
  (* update of an array of size [s1] *)
  | Eslice : exp * size * size -> exp  (* e{s1..s2} *)
  | Econcat : exp * size * exp * size -> exp  (* { e1 | e2 } *)
  | Evec : exp * size -> exp
  (* e1[e2] build an array of size [s2] with value [e1] *)
  | Etuple: exp list -> exp
  | Erecord: exp record list -> exp
  | Erecord_access: exp record -> exp
  | Erecord_with: exp * exp record list -> exp
  | Eifthenelse: exp * exp * exp -> exp
  | Ematch: exp * (pattern, exp) match_handler list -> exp
  | Elet: pattern * exp * exp -> exp
  | Eletvar : { id: Ident.t; is_mutable: is_mutable;
                ty: Deftypes.typ; e_opt: exp option; e : exp } -> exp
  | Eassign: left_value * exp -> exp(* [x.v <- ...] *)
  | Eassign_state: left_state_value * exp -> exp(* [x.v <- ...] *)
  | Esequence: exp list -> exp
  | Eapp: exp * exp list -> exp
  | Emethodcall: methodcall -> exp
  | Etypeconstraint: exp * type_expression -> exp
  | Efor: Ident.t * exp * exp * exp -> exp
  | Ewhile: exp * exp -> exp
  | Emachine: pattern list * machine -> exp
  | Efun: pattern list * exp -> exp
                    
(* when [is_mutable = true] a variable [x] is mutable which means that *)
 (* x <- ... and ...x... are valid expression; otherwise a ref will be *)
 (* added when translated into OCaml **)
and is_mutable = bool

and left_value = 
  | Eleft_name of Ident.t
  | Eleft_record_access of left_value * Lident.t
  | Eleft_index of left_value * exp
  
and left_state_value =
  | Eself
  | Eleft_state_global of Lident.t 
  | Eleft_instance_name of Ident.t
  | Eleft_state_name of Ident.t
  | Eleft_state_record_access of left_state_value * Lident.t
  | Eleft_state_index of left_state_value * exp
  | Eleft_state_primitive_access of left_state_value * mkind


and left_value = 
  | Oleft_name of Ident.t
  | Oleft_record_access of left_value * Lident.t
  | Oleft_index of left_value * exp
  
and left_state_value =
  | Oself
  | Oleft_state_global of Lident.t 
  | Oleft_instance_name of Ident.t
  | Oleft_state_name of Ident.t
  | Oleft_state_record_access of left_state_value * Lident.t
  | Oleft_state_index of left_state_value * exp
  | Oleft_state_primitive_access of left_state_value * primitive_access

(* a machine provides certain fields for reading/writting state variables *)
and primitive_access =
  | Oder (* x.der.(i) <- ... *)
  | Ocont (* x.pos.(i) <- ... *)
  | Ozero_out (* x.zero_out.(i) <-... *)
  | Ozero_in (* ... x.zero_in.(i) ... *)

(* Definition of a sequential machine *)
and machine =
  { ma_kind: Deftypes.kind;
    (* combinatorial, continuous-time or discrete-time *)
    ma_params: pattern list; (* list of static parameters *)
    ma_memories: mentry list;(* its memories *)
    ma_instances: ientry list; (* its node instances *)
    ma_methods: method_desc list; (* its methods *) 
  }

and mentry =
  { m_name: Ident.t; (* its name *)
    m_value: exp option; (* its initial value *)
    m_typ: Deftypes.typ; (* its type *)
    m_kind: mkind; (* the kind of the memory *)
    m_size: exp path; (* it may be an array *)
  }

and ientry =
  { i_name: Ident.t; (* its name *)
    i_machine: exp;  (* the machine it belongs to *)
    i_kind: Deftypes.kind; (* the kind of the machine *)
    i_params: exp path; (* static parameters used at instance creation *)
    i_size: exp list; (* it is possibly an array of instances *)
  }
    
and method_desc =
  { me_name: method_name; (* name of the method *)
    me_params: pattern list; (* list of input arguments *)
    me_body: exp; (* its result *)
    me_typ: Deftypes.typ; (* type of the result *)
  }

and methodcall =
  { met_machine: Lident.t option; (* the class of the method *)
    met_name: method_name; (* name of the method *)
    met_instance: (Ident.t * exp path) option;
    (* either a call to self (None) or to *)
    (* one instance o.(index_1)...(index_n).m(e_1,...,e_k) *)
    met_args: exp list;
  }

and method_name = name

(* The different kinds of state variables *)
and mkind =
  | Eder (* x.der <- ... *)
  | Econt (* x.pos <- ... *)
  | Ezout (* x.zout <-... *)
  | Ezin (* ... x.zin ... *)
  | Ediscrete (* x <- *)
        
and 'a path = 'a list

and implementation_list = implementation list

and implementation = 
  | Eletdef of name * exp
  | Eopen of string
  | Etypedecl of (string * string list * type_decl) list

and info = type_expression

(* type declaration *)
and type_expression = 
  | Etypevar of name
  | Etypefun of kind * type_expression * type_expression
  | Etypetuple of type_expression list
  | Etypeconstr of Lident.t * type_expression list
  | Etypevec of type_expression * size
  | Etypesize of is_singleton * size

and kind = Ekind_fun | Ekind_node 

and type_decl =
  | Eabstract_type
  | Eabbrev of type_expression
  | Evariant_type of constr_decl list
  | Erecord_type of (string * type_expression) list
					       
and constr_decl =
  | Econstr0decl of string
  | Econstr1decl of string * type_expression list

and is_singleton = bool

and size =
  | Sconst of int
  | Svar of Ident.t
  | Splus of size * size
  | Sminus of size * size
  | Sdiv of { num: size; denom: int }
