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

type 'a localized = { desc: 'a; loc: Location.t }

type name = String.t

(** kinds *)
type kind =
  | Knode : tkind -> kind (* stateful *)
  | Kfun : vkind -> kind (* combinatorial *)

and vkind =
  | Kconst (* constant; known at compilation time *)
  | Kstatic (* constant; known at instantiation time *)
  | Kany (* known dynamically *)

and tkind =
  | Kdiscrete (* only discrete-time state variables *)
  | Khybrid (* discrete-time and continuous-time state variables *)

(** Types *)
type type_expression = type_expression_desc localized

and type_expression_desc =
  | Etypevar : name -> type_expression_desc
  | Etypeconstr : Lident.t * type_expression list -> type_expression_desc
  | Etypetuple : type_expression list -> type_expression_desc
  | Etypefun : kind * type_expression * type_expression -> type_expression_desc

(* constants *)
type immediate =
| Eint : int -> immediate
| Ebool : bool -> immediate
| Efloat : float -> immediate
| Evoid : immediate
| Echar : char -> immediate
| Estring : string -> immediate

(* synchronous operators *)
type operator =
  | Efby : operator
  (* unit delay *)
  | Eunarypre : operator
  (* unit delay *)
  | Eifthenelse : operator
  (* mux *)
  | Eminusgreater : operator
  (* initialization *)
  | Eseq : operator
  (* sequence *)
  | Erun : is_inline -> operator
  (* application of a statefull function *)
  | Eatomic : operator
  (* the argument is atomic *)
  | Etest : operator
  (* testing the presence of a signal *)
  | Eup : operator
  (* zero-crossing detection *)
  | Eperiod : operator
  (* period *)
  | Ehorizon : operator
  (* generate an event at a given horizon *)
  | Edisc : operator
  (* generate an event whenever x <> last x outside of integration *)
  | Earray : array_operator -> operator

and array_operator =
  | Earray_list : array_operator
  (* [| e1;...;en |] *)
  | Econcat : array_operator
  (* [ e1 ++ e2] *)
  | Eget : array_operator
  (* [e.(e)] *)
  | Eget_with_default : array_operator
  (* [e.(e) default e] *)
  | Eslice : array_operator
  (* [e.(e .. e)] *)
  | Eupdate : array_operator
  (* [| e with e <- e |] *)
  | Etranspose : array_operator
  (* [e.T] *)
  | Eflatten : array_operator
  (* [e.F] *)
  | Ereverse : array_operator
  (* [e.R] *)

and is_inline = bool

type pateq = pateq_desc localized

and pateq_desc = Ident.t list

type 'exp vardec =
  { var_name: Ident.t; (* its name *)
    var_default: 'exp option; (* possible default value *)
    var_init: 'exp option; (* possible initial value for [last x] *)
    var_clock: bool; (* is-it a clock name ? *)
    var_loc: Location.t;
    var_typeconstraint: type_expression option;
    var_is_last: bool; (* is-there an access to [last x] ? *)
  }

type 'a record = { mutable label: Lident.t; arg: 'a }

type 'info pattern =
  { mutable pat_desc: 'info pattern_desc; (* descriptor *)
    pat_loc: Location.t; (* its location in the source file *)
    pat_info: 'info; (* info *)
  }

and 'info pattern_desc = 
  | Etuplepat : 'info pattern list -> 'info pattern_desc 
  | Evarpat : Ident.t -> 'info pattern_desc 
  | Ewildpat : 'info pattern_desc 
  | Econstpat : immediate -> 'info pattern_desc 
  | Econstr0pat : Lident.t -> 'info pattern_desc 
  | Econstr1pat : Lident.t * 'info pattern list -> 'info pattern_desc 
  | Ealiaspat : 'info pattern * Ident.t -> 'info pattern_desc 
  | Eorpat : 'info pattern * 'info pattern -> 'info pattern_desc 
  | Erecordpat : 'info pattern record list -> 'info pattern_desc 
  | Etypeconstraintpat : 'info pattern * type_expression -> 'info pattern_desc 

type ('info, 'exp, 'eq) block =
  { b_vars: 'exp vardec list;
    b_body: 'eq;
    b_loc: Location.t;
    mutable b_write: Defnames.defnames;
    b_env: 'info Ident.Env.t;
  }

(* state name of an automaton; possibly parameterized *)
type statepatdesc =
  | Estate0pat : Ident.t -> statepatdesc 
  | Estate1pat : Ident.t * Ident.t list -> statepatdesc

type statepat = statepatdesc localized

type 'exp state_desc =
  | Estate0 : Ident.t -> 'exp state_desc
  | Estate1 : Ident.t * 'exp list -> 'exp state_desc
  | Estateif : 'exp * 'exp state * 'exp state -> 'exp state_desc

and 'exp state = 'exp state_desc localized

(* the body of a pattern matching *)
type ('info, 'body) match_handler =
  { m_pat : 'info pattern;
    m_body: 'body;
    m_loc: Location.t;
    m_reset: bool; (* the handler is reset on entry *)
    m_zero: bool; (* the handler is done at a zero-crossing instant *)
    m_env: 'info Ident.Env.t;
  }

(* the body of a present handler *)
type ('info, 'scondpat, 'body) present_handler =
  { p_cond: 'scondpat;
    p_body: 'body;
    p_loc: Location.t;
    p_env: 'info Ident.Env.t;
    p_zero: bool;
  }

type ('info, 'scondpat, 'exp, 'leq, 'body) escape =
  { e_cond: 'scondpat;
    e_reset: bool;
    e_let: 'leq list;
    e_body: 'body;
    e_next_state: 'exp state;
    e_loc: Location.t;
    e_env: 'info Ident.Env.t;
  }

type is_weak = bool

(* sizes for arrays and bounded recursions - only multivariate polynomials *)
type size = size_desc localized

and size_desc =
  | Sint : int -> size_desc
  | Sfrac : { num: size; denom: int } -> size_desc
  | Sident : Ident.t -> size_desc
  | Splus: size * size -> size_desc
  | Sminus : size * size -> size_desc
  | Smult: size * size -> size_desc
  
type 'info exp =
  { e_desc: 'info exp_desc; (* descriptor *)
    e_loc: Location.t; (* location *)
    e_info: 'info; (* information *)
  }

and 'info exp_desc =
  | Econst : immediate -> 'info exp_desc
  | Econstr0 : { mutable lname: Lident.t } -> 'info exp_desc
  | Econstr1 :
      { mutable lname: Lident.t; arg_list: 'info exp list } -> 'info exp_desc
  | Evar : Ident.t -> 'info exp_desc
  | Eglobal :
      { mutable lname : Lident.t } -> 'info exp_desc
  | Elast : Ident.t -> 'info exp_desc
  | Eop : operator * 'info exp list -> 'info exp_desc
  | Etuple : 'info exp list -> 'info exp_desc
  | Eapp : { is_inline: is_inline; f: 'info exp; arg_list: 'info exp list } -> 'info exp_desc
  | Esizeapp : { f: 'info exp; size_list: size list } -> 'info exp_desc
  | Elet : 'info leq * 'info exp -> 'info exp_desc
  | Elocal : ('info, 'info exp, 'info eq) block * 'info exp -> 'info exp_desc
  | Erecord_access : 'info exp record -> 'info exp_desc
  | Erecord : 'info exp record list -> 'info exp_desc
  | Erecord_with : 'info exp * 'info exp record list -> 'info exp_desc
  | Etypeconstraint : 'info exp * type_expression -> 'info exp_desc
  | Efun : 'info funexp -> 'info exp_desc
  | Ematch : { mutable is_total : bool; e : 'info exp;
               handlers : ('info, 'info exp) match_handler list } -> 
      'info exp_desc
  | Epresent :
      { handlers : ('info, 'info scondpat, 'info exp) present_handler list;
        default_opt : 'info exp default } -> 'info exp_desc
  | Ereset : 'info exp * 'info exp -> 'info exp_desc
  | Eassert : 'info exp -> 'info exp_desc
  | Eforloop : ('info, 'info exp, 'info for_exp) forloop -> 'info exp_desc

and ('info, 'size, 'body) forloop =
  { for_size : 'size option;
    for_kind : 'info for_kind;
    for_index : Ident.t option;
    for_input : 'info for_input_desc localized list;
    for_body : 'body;
    for_resume : bool; (* resume or restart *)
    for_env : 'info Ident.Env.t;
  }

(* result expression of a loop *)
and 'info for_exp =
  | Forexp : { exp : 'info exp; default : 'info exp option } -> 'info for_exp
  (* [for[each|ward] ... do e done] *)
  | Forreturns :
      { returns : 'info exp for_vardec_desc localized list; (* return *)
        body : ('info, 'info exp, 'info eq) block; (* body *)
        r_env : 'info Ident.Env.t; (* environment *)
      } -> 'info for_exp
(* [for[each|ward] ... returns (...) local ... do eq ... done] *)

and 'exp for_vardec_desc =
  { for_array : int; (* 0 means x; 1 means [|x|]; 2 means [|[| x|]|]; etc *)
    for_vardec : 'exp vardec; (* [x [init e] [default e]] *)
  }

and is_rec = bool

and 'info leq =
  { l_kind: vkind;
    l_rec: is_rec;
    l_eq: 'info eq;
    l_loc : Location.t;
    l_env: 'info Ident.Env.t;
  }

and 'info eq =
  { eq_desc: 'info eq_desc; (* descriptor *)
    mutable eq_write: Defnames.defnames; (* set of defined variables *)
    eq_loc: Location.t; (* its location *)
  }

and 'info eq_desc =
  | EQeq : 'info pattern * 'info exp -> 'info eq_desc  (* [p = e] *)
  (* a size-parameterized expression [id <n1,...,nk> = e] *)
  | EQsizefun : 'info sizefun -> 'info eq_desc
  | EQder :
      { id: Ident.t; e: 'info exp; e_opt: 'info exp option;
        handlers: ('info, 'info scondpat, 'info exp) present_handler list }
      -> 'info eq_desc  (* [der x = e [init e0] [reset z1 -> e1 | ...]] *)
  | EQinit : Ident.t * 'info exp -> 'info eq_desc  (* [init x = e] *)
  | EQemit : Ident.t * 'info exp option -> 'info eq_desc  (* [emit x [= e]] *)
  (* [if e then eq1 else eq2] *)
  | EQif : { e: 'info exp; eq_true: 'info eq; eq_false: 'info eq } -> 
      'info eq_desc 
  | EQand : 'info eq list -> 'info eq_desc (* [eq1 and...and eqn] *)
  | EQlocal : ('info, 'info exp, 'info eq) block -> 
      'info eq_desc (* local x [...] do eq done *)
  | EQlet : 'info leq * 'info eq -> 'info eq_desc (* let eq in eq *)
  | EQreset : 'info eq * 'info exp -> 'info eq_desc (* [reset eq every e] *)
  | EQautomaton :
      { is_weak : bool;
        handlers : ('info,
                    ('info, 'info exp, 'info eq) block) automaton_handler list;
        state_opt : 'info exp state option } -> 'info eq_desc
  | EQpresent :
      { handlers : ('info, 'info scondpat, 'info eq) present_handler list;
        default_opt : 'info eq default } -> 'info eq_desc
  | EQmatch : { mutable is_total : bool; e : 'info exp;
                handlers : ('info, 'info eq) match_handler list } -> 
      'info eq_desc
  | EQempty : 'info eq_desc
  | EQassert : 'info exp -> 'info eq_desc
  | EQforloop : ('info, 'info exp, 'info for_eq) forloop -> 'info eq_desc
(* [foreach [e]* [id in e [by e],]* returns (vardec_list) do eq] *)
(* [forward [resume] [e]* [id in e [by e],]* returns (vardec_list) *)
(*  do eq [while/unless/until e] e done]  *)

and 'info for_eq =
  { for_out : 'info for_out_desc localized list;
    for_block : ('info, 'info exp, 'info eq) block; (* loop body *)
  }

and 'info for_kind =
  | Kforeach : 'info for_kind
  (* parallel loop *)
  | Kforward : 'info for_exit option -> 'info for_kind
(* iteration during one instant. The argument is the stoping condition *)

and 'info for_exit = 
  { for_exit : 'info exp;
    for_exit_kind : for_exit_kind }

and for_exit_kind = 
  | Ewhile | Euntil | Eunless

(* input definition for a loop *)
and 'info for_input_desc =
  (* xi in e1 [by e2], that is, xi = e1.(i * e2) *)
  | Einput : { id: Ident.t; e : 'info exp; by : 'info exp option } -> 
      'info for_input_desc
  (* [i in e1 to e2] or [i in e1 downto e2]; [e1] and [e2] must be sizes *)
  | Eindex :
      { id: Ident.t; e_left: 'info exp; e_right : 'info exp; dir: bool } -> 
      'info for_input_desc

(* output of a for loop in equational form *)
and 'info for_out_desc =
  { for_name : Ident.t; (* xi [init e] [default e] [out x] *)
    for_out_name : Ident.t option; (* [xi out x] *)
    for_init : 'info exp option;
    for_default : 'info exp option;
  }

(* signal patterns *)
and 'info scondpat = 'info scondpat_desc localized

and 'info scondpat_desc =
  | Econdand : 'info scondpat * 'info scondpat -> 'info scondpat_desc
  | Econdor : 'info scondpat * 'info scondpat -> 'info scondpat_desc
  | Econdexp : 'info exp -> 'info scondpat_desc
  | Econdpat : 'info exp * 'info pattern -> 'info scondpat_desc
  | Econdon : 'info scondpat * 'info exp -> 'info scondpat_desc

and ('info, 'body) automaton_handler =
  { s_state: statepat;
    s_let: 'info leq list;
    s_body: 'body;
    s_trans: ('info, 'info scondpat, 'info exp, 'info leq, 'body) escape list;
    s_loc: Location.t;
    mutable s_reset: bool; (* is the state always entered by reset? *)
    s_env: 'info Ident.Env.t; (* env. for parameter names in [s_state] *) 
  }

and 'a default =
  | Init : 'a -> 'a default | Else : 'a -> 'a default | NoDefault

and is_atomic = bool

and 'info funexp =
  { f_vkind: vkind; (* the kind of arguments *)
    f_kind: kind; (* the kind of the body *)
    f_atomic: is_atomic; (* when true, outputs depend strictly on all inputs *)
    f_args: 'info arg list; (* list of arguments *)
    f_body: 'info result;
    f_loc: Location.t;
    f_env: 'info Ident.Env.t;
  }

and 'info sizefun =
  { sf_id: Ident.t;
    sf_id_list: Ident.t list;
    sf_e : 'info exp;
    sf_loc: Location.t;
    sf_env: 'info Ident.Env.t;
  }

and 'info arg = 'info exp vardec list

and 'info result =
  { r_desc: 'info result_desc;
    r_loc: Location. t }

and 'info result_desc =
  | Exp: 'info exp -> 'info result_desc
  | Returns: ('info, 'info exp, 'info eq) block -> 'info result_desc


(** Declarations *)
type interface = interface_desc localized

and interface_desc =
  | Einter_open : name -> interface_desc
  | Einter_typedecl :
      { name: name; ty_params: name list; size_params: name list;
        ty_decl: type_decl } -> interface_desc
  | Einter_constdecl :
      { name: name; const: bool; ty: type_expression; info: name list }
      -> interface_desc

and type_decl = type_decl_desc localized

and type_decl_desc =
  | Eabstract_type : type_decl_desc
  | Eabbrev : type_expression -> type_decl_desc
  | Evariant_type : constr_decl list -> type_decl_desc
  | Erecord_type : (name * type_expression) list -> type_decl_desc

and constr_decl = constr_decl_desc localized

and constr_decl_desc =
  | Econstr0decl : name -> constr_decl_desc
  | Econstr1decl : name * type_expression list -> constr_decl_desc

type 'info implementation = 'info implementation_desc localized

and 'info implementation_desc =
  | Eopen : name -> 'info implementation_desc
  (* names defined globally and equations *)
  | Eletdecl : { d_names: (name * Ident.t) list; d_leq: 'info leq } -> 
      'info implementation_desc
  | Etypedecl :
      { name: name; ty_params: name list; size_params: name list;
        ty_decl: type_decl } -> 'info implementation_desc

type 'info program = 
  { p_impl_list : 'info implementation list;
    p_index : Ident.num }

