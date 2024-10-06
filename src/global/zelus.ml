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

(* The mais ast. types are parameterized by two types variables *)
(* ['info] and ['env]; the first is the information attached to expressions *)
(* the second is the containt of an environment (an environment associate *)
(* a value to a name *)

type 'a localized = { desc: 'a; loc: Location.t }

type name = String.t

(** kinds *)
type kind =
  | Knode of tkind (* stateful *)
  | Kfun of vkind (* combinatorial *)

and vkind =
  | Kconst (* constant; known at compilation time *)
  | Kstatic (* constant; known at instantiation time *)
  | Kany (* known dynamically *)

and tkind =
  | Kdiscrete (* only discrete-time state variables *)
  | Kcont (* discrete-time and continuous-time state variables *)

(** Types *)
type type_expression = type_expression_desc localized

and type_expression_desc =
  | Etypevar of name
  | Etypeconstr of Lident.t * type_expression list
  | Etypetuple of type_expression list
  | Etypefun of
      { ty_kind: kind; ty_name_opt: Ident.t option;
        ty_arg : type_expression; ty_res : type_expression }
  (* array: [size]t defines an array of size [t] with values of type [t] *)
  | Etypevec of type_expression * size_expression

and is_singleton = bool

(* sizes for arrays and bounded recursions - only multivariate polynomials *)
and size_expression = size_expression_desc localized

and size_expression_desc =
  | Size_int of int
  | Size_var of Ident.t
  | Size_frac of { num: size_expression; denom: int }
  | Size_op of op * size_expression * size_expression 

and op = | Size_plus | Size_minus | Size_mult 

(* the two forms of [last]; [last x] and [last* x] *)
type last =
  { copy: bool; (* [copy = false] (that is, [last* x] *)
    id: Ident.t; (* means that [x] and [last* x] share the same location *)
    }

(* constants *)
type immediate =
| Eint of int
| Ebool of bool
| Efloat of float
| Evoid
| Echar of char
| Estring of string

(* synchronous operators *)
type operator =
  | Efby
  (* unit delay - arity = 2 *)
  | Eunarypre
  (* unit delay - arity = 1 *)
  | Eifthenelse
  (* mux *)
  | Eminusgreater
  (* initialization - arity = 2 *)
  | Eseq
  (* sequence - arity = n *)
  | Erun of is_inline 
  (* application of a statefull function - arity = 1 *)
  | Eatomic 
  (* the argument is atomic - arity = 1 *)
  | Etest 
  (* testing the presence of a signal - arity = 1 *)
  | Eup 
  (* zero-crossing detection - arity = 1 *)
  | Eperiod 
  (* period - arity = 2 *)
  | Ehorizon 
  (* generate an event at a given horizon - arity = 1 *)
  | Edisc 
  (* generate an event whenever x <> last x outside of integration *)
  | Earray of array_operator

and array_operator =
  | Earray_list 
  (* [| e1;...;en |] *)
  | Econcat 
  (* [ e1 ++ e2] *)
  | Eget 
  (* [e.(e)] *)
  | Eget_with_default 
  (* [e.(e) default e] *)
  | Eslice 
  (* [e.(e .. e)] *)
  | Eupdate 
  (* [| e with e <- e |] *)
  | Etranspose 
  (* [e.T] *)
  | Eflatten 
  (* [e.F] *)
  | Ereverse 
  (* [e.R] *)

and is_inline = bool

type pateq = pateq_desc localized

and pateq_desc = Ident.t list

type 'a init =
  | Init of 'a (* the variable is declared with an initial value *)
  | InitEq (* the initialization is deferred to the body *)
  | Last (* [last x] is allowed but not initialization is given *)

type ('info, 'exp) vardec =
  { var_name: Ident.t; (* its name *)
    var_default: 'exp option; (* possible default value *)
    var_init: 'exp option; (* possible initial value for [last x] *)
    var_clock: bool; (* is-it a clock name ? *)
    var_loc: Location.t;
    var_typeconstraint: type_expression option;
    var_is_last: bool; (* is-there an access to [last x] ? *)
    var_init_in_eq: bool; (* the initialization is later in the body *)
    mutable var_info : 'info; (* information *)
  }

type 'a record = { mutable label: Lident.t; arg: 'a }

type 'info pattern =
  { mutable pat_desc: 'info pattern_desc; (* descriptor *)
    pat_loc: Location.t; (* its location in the source file *)
    mutable pat_info: 'info; (* info *)
  }

and 'info pattern_desc = 
  | Etuplepat of 'info pattern list
  | Evarpat of Ident.t 
  | Ewildpat
  | Econstpat of immediate 
  | Econstr0pat of Lident.t 
  | Econstr1pat of Lident.t * 'info pattern list 
  | Ealiaspat of 'info pattern * Ident.t 
  | Eorpat of 'info pattern * 'info pattern 
  | Erecordpat of 'info pattern record list 
  | Etypeconstraintpat of 'info pattern * type_expression 

type ('info, 'env, 'exp, 'eq) block =
  { b_vars: ('info, 'exp) vardec list;
    b_body: 'eq;
    b_loc: Location.t;
    mutable b_write: Defnames.defnames;
    mutable b_env: 'env Ident.Env.t;
  }

(* state name of an automaton; possibly parameterized *)
type statepatdesc =
  | Estate0pat of Ident.t 
  | Estate1pat of Ident.t * Ident.t list 

type statepat = statepatdesc localized

type 'exp state_desc =
  | Estate0 of Ident.t 
  | Estate1 of Ident.t * 'exp list 
  | Estateif of 'exp * 'exp state * 'exp state 

and 'exp state = 'exp state_desc localized

(* the body of a pattern matching *)
type ('env, 'pattern, 'body) match_handler =
  { m_pat : 'pattern;
    m_body: 'body;
    m_loc: Location.t;
    m_reset: bool; (* the handler is reset on entry *)
    m_zero: bool; (* the handler is done at a zero-crossing instant *)
    mutable m_env: 'env Ident.Env.t;
  }

(* the body of a present handler *)
type ('env, 'scondpat, 'body) present_handler =
  { p_cond: 'scondpat;
    p_body: 'body;
    p_loc: Location.t;
    mutable p_env: 'env Ident.Env.t;
    p_zero: bool;
  }

type ('env, 'scondpat, 'exp, 'leq, 'body) escape =
  { e_cond: 'scondpat;
    e_reset: bool;
    e_let: 'leq list;
    e_body: 'body;
    e_next_state: 'exp state;
    e_loc: Location.t;
    e_zero: bool;
    mutable e_env: 'env Ident.Env.t;
  }

type is_weak = bool

type ('info, 'env) exp =
  { e_desc: ('info, 'env) exp_desc; (* descriptor *)
    e_loc: Location.t; (* location *)
    mutable e_info: 'info; (* information *)
  }

and ('info, 'env) exp_desc =
  | Econst of immediate
  | Econstr0 of { mutable lname : Lident.t }
  | Econstr1 of
      { mutable lname : Lident.t; arg_list: ('info, 'env) exp list }
  | Evar of Ident.t
  | Eglobal of
      { mutable lname : Lident.t }
  | Elast of last
  | Eop of operator * ('info, 'env) exp list
  | Etuple of ('info, 'env) exp list
  | Eapp of { is_inline: is_inline; f: ('info, 'env) exp;
              arg_list: ('info, 'env) exp list }
  | Esizeapp of
      { f: ('info, 'env) exp; size_list: size_expression list }
  | Elet of ('info, 'env) leq * ('info, 'env) exp
  | Elocal of ('info, 'env, ('info, 'env) exp, ('info, 'env) eq) block
              * ('info, 'env) exp
  | Erecord_access of ('info, 'env) exp record
  | Erecord of ('info, 'env) exp record list
  | Erecord_with of ('info, 'env) exp * ('info, 'env) exp record list
  | Etypeconstraint of ('info, 'env) exp * type_expression 
  | Efun of ('info, 'env) funexp 
  | Ematch of { mutable is_total : bool; e : ('info, 'env) exp;
                handlers : ('env, 'info pattern, ('info, 'env) exp)
                             match_handler list } 
  | Epresent of
      { handlers : ('env, ('info, 'env) scondpat, ('info, 'env) exp)
                     present_handler list;
        default_opt : ('info, 'env) exp default } 
  | Ereset of ('info, 'env) exp * ('info, 'env) exp 
  | Eassert of ('info, 'env) exp
  | Eforloop of ('info, 'env, ('info, 'env) exp, ('info, 'env) for_exp) forloop 

and ('info, 'env, 'size, 'body) forloop =
  { for_size : 'size option;
    for_kind : ('info, 'env) exp for_kind;
    for_index : Ident.t option;
    for_input : ('info, 'env) exp for_input list;
    for_body : 'body;
    for_resume : bool; (* resume or restart *)
    for_env : 'env Ident.Env.t; (* names (index and inputs) *)
  }

(* result expression of a loop *)
and ('info, 'env) for_exp =
  | Forexp of { exp : ('info, 'env) exp; default : ('info, 'env) exp option } 
  (* [for[each|ward] ... do e done] *)
  | Forreturns of ('info, 'env) for_returns 

and ('info, 'env) for_returns =
  { r_returns : ('info, 'env) for_vardec list; (* return *)
    r_block : ('info, 'env, ('info, 'env) exp, ('info, 'env) eq) block;
    (* body *)
    r_env : 'env Ident.Env.t; (* environment for the return *)
    (* [for[each|ward] ... returns (...) local ... do eq ... done] *)
  }

and ('info, 'env) for_vardec = ('info, 'env) for_vardec_desc localized

and ('info, 'env) for_vardec_desc =
  { for_array : int; (* 0 means x; 1 means [|x|]; 2 means [|[| x|]|]; etc *)
    for_vardec : ('info, ('info, 'env) exp) vardec;
    (* [x [init e] [default e]] *)
  }

and is_rec = bool

and ('info, 'env) leq =
  { l_kind: vkind;
    l_rec: is_rec;
    l_eq: ('info, 'env) eq;
    l_loc : Location.t;
    mutable l_env: 'env Ident.Env.t;
  }

and ('info, 'env) eq =
  { eq_desc: ('info, 'env) eq_desc; (* descriptor *)
    mutable eq_write: Defnames.defnames; (* set of defined variables *)
    eq_index: int;
    (* a unique index; used to build a partial order between eqs *)
    eq_safe: bool; (* the equation calls a possibly unsafe computation *)
    eq_loc: Location.t; (* its location *)
  }

and ('info, 'env) eq_desc =
  | EQeq of 'info pattern * ('info, 'env) exp (* [p = e] *)
  (* a size-parameterized expression [id <n1,...,nk> = e] *)
  | EQsizefun of ('info, 'env) sizefun 
  | EQder of
      { id: Ident.t; e: ('info, 'env) exp; e_opt: ('info, 'env) exp option;
        handlers: ('env, ('info, 'env) scondpat, ('info, 'env) exp)
                    present_handler list }
    (* [der x = e [init e0] [reset z1 -> e1 | ...]] *)
  | EQinit of Ident.t * ('info, 'env) exp (* [init x = e] *)
  | EQemit of Ident.t * ('info, 'env) exp option (* [emit x [= e]] *)
  (* [if e then eq1 else eq2] *)
  | EQif of { e: ('info, 'env) exp;
              eq_true: ('info, 'env) eq;
              eq_false: ('info, 'env) eq } 
  | EQand of { ordered: bool; eq_list: ('info, 'env) eq list } 
  (* [eq1 and...and eqn] when [ordered], side effects must be done *)
  (* in order, from left to right *)
  | EQlocal of ('info, 'env, ('info, 'env) exp, ('info, 'env) eq) block
  (* local x [...] do eq done *)
  | EQlet of ('info, 'env) leq * ('info, 'env) eq (* let eq in eq *)
  | EQreset of ('info, 'env) eq * ('info, 'env) exp (* [reset eq every e] *)
  | EQautomaton of
      { is_weak : bool;
        handlers : ('info, 'env,
                    ('info, 'env, ('info, 'env) exp, ('info, 'env) eq) block)
                     automaton_handler list;
        state_opt : ('info, 'env) exp state option } 
  | EQpresent of
      { handlers : ('env, ('info, 'env) scondpat, ('info, 'env) eq)
                     present_handler list;
        default_opt : ('info, 'env) eq default } 
  | EQmatch of { mutable is_total : bool; e : ('info, 'env) exp;
                 handlers : ('env, 'info pattern, ('info, 'env) eq)
                              match_handler list }
  | EQempty
  | EQassert of ('info, 'env) exp 
  | EQforloop of ('info, 'env, ('info, 'env) exp, ('info, 'env) for_eq) forloop 
(* [foreach [e]* [id in e [by e],]* returns (vardec_list) do eq] *)
(* [forward [resume] [e]* [id in e [by e],]* returns (vardec_list) *)
(*  do eq [while/unless/until e] e done]  *)

and ('info, 'env) for_eq =
  { for_out : ('info, 'env) for_out list; (* outputs *)
    (* loop body *)
    for_block : ('info, 'env, ('info, 'env) exp, ('info, 'env) eq) block; 
    mutable for_out_env: 'env Ident.Env.t; (* names in output *)
  }

and 'exp for_kind =
  | Kforeach
  (* parallel loop *)
  | Kforward of 'exp for_exit option 
(* iteration during one instant. The argument is the stoping condition *)

and 'exp for_exit = 
  { for_exit : 'exp;
    for_exit_kind : for_exit_kind }

and for_exit_kind = | Ewhile | Euntil | Eunless

(* input definition for a loop *)
and 'exp for_input = 'exp for_input_desc localized

and 'exp for_input_desc =
  (* xi in e1 [by e2], that is, xi = e1.(i * e2) *)
  | Einput of { id: Ident.t; e : 'exp; by : 'exp option } 
  (* [i in e1 to e2] or [i in e1 downto e2]; [e1] and [e2] must be sizes *)
  | Eindex of
      { id: Ident.t; e_left: 'exp; e_right : 'exp; dir: bool } 

(* output of a for loop in equational form *)
and ('info, 'env) for_out = ('info, 'env) for_out_desc localized

and ('info, 'env) for_out_desc =
  { for_name : Ident.t; (* xi [init e] [default e] [out x] *)
    for_out_name : Ident.t option; (* [xi out x] *)
    for_init : ('info, 'env) exp option;
    for_default : ('info, 'env) exp option;
  }

(* signal patterns *)
and ('info, 'env) scondpat = ('info, 'env) scondpat_desc localized

and ('info, 'env) scondpat_desc =
  | Econdand of ('info, 'env) scondpat * ('info, 'env) scondpat 
  | Econdor of ('info, 'env) scondpat * ('info, 'env) scondpat 
  | Econdexp of ('info, 'env) exp
  | Econdpat of ('info, 'env) exp * 'info pattern 
  | Econdon of ('info, 'env) scondpat * ('info, 'env) exp 

and ('info, 'env, 'body) automaton_handler =
  { s_state: statepat;
    s_let: ('info, 'env) leq list;
    s_body: 'body;
    s_trans: ('env, ('info, 'env) scondpat, ('info, 'env) exp,
              ('info, 'env) leq, 'body) escape list;
    s_loc: Location.t;
    mutable s_reset: bool; (* is the state always entered by reset? *)
    mutable s_env: 'env Ident.Env.t;
    (* env. for parameter names in [s_state] *) 
  }

and 'a default = | Init of 'a | Else of 'a | NoDefault

and is_atomic = bool

and ('info, 'env) funexp =
  { f_vkind: vkind; (* the kind of arguments *)
    f_kind: kind; (* the kind of the body *)
    f_atomic: is_atomic; (* when true, outputs depend strictly on all inputs *)
    f_args: ('info, 'env) arg list; (* list of arguments *)
    f_body: ('info, 'env) result;
    f_loc: Location.t;
    mutable f_env: 'env Ident.Env.t;
  }

and ('info, 'env) sizefun =
  { sf_id: Ident.t;
    sf_id_list: Ident.t list;
    sf_e : ('info, 'env) exp;
    sf_loc: Location.t;
    mutable sf_env: 'env Ident.Env.t;
  }

and ('info, 'env) arg = ('info, ('info, 'env) exp) vardec list

and ('info, 'env) result =
  { r_desc: ('info, 'env) result_desc;
    r_loc: Location.t;
    mutable r_info: 'info }

and ('info, 'env) result_desc =
  | Exp of ('info, 'env) exp 
  | Returns of ('info, 'env, ('info, 'env) exp, ('info, 'env) eq) block


(** Declarations *)
type interface = interface_desc localized

and interface_desc =
  | Einter_open of name 
  | Einter_typedecl of
      { name: name; ty_params: name list; ty_decl: type_decl } 
  | Einter_constdecl of
      { name: name; const: bool; ty: type_expression; info: name list }

and type_decl = type_decl_desc localized

and type_decl_desc =
  | Eabstract_type
  | Eabbrev of type_expression 
  | Evariant_type of constr_decl list 
  | Erecord_type of (name * type_expression) list

and constr_decl = constr_decl_desc localized

and constr_decl_desc =
  | Econstr0decl of name 
  | Econstr1decl of name * type_expression list 

type ('info, 'env) implementation = ('info, 'env) implementation_desc localized

and ('info, 'env) implementation_desc =
  | Eopen of name 
  (* names defined globally and equations *)
  | Eletdecl of { d_names: (name * Ident.t) list; d_leq: ('info, 'env) leq } 
  | Etypedecl of
      { name: name; ty_params: name list;  ty_decl: type_decl } 

type ('info, 'env) program = 
  { p_impl_list : ('info, 'env) implementation list;
    p_index : Ident.num }

