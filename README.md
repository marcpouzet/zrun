# The ZRun Synchronous Language Interpreter

ZRun is an executable reference semantics for a synchronous data-flow
language. It takes the form of an interpreted expressed in a purely
functional manner and is implemented in OCaml. The input of Zrun is a
large subset of the language [Zélus](https://zelus.di.ens.fr). Only
the discrete-time (synchronous) subset is considered for the moment,
that is, signals are infinite streams and systems are stream
functions. The basic primitives and the semantics principles of the language are those
of [Lustre](https://www-verimag.imag.fr/The-Lustre-Programming-Language-and?lang=en)
(e.g., the non initialized unit delay (pre), initialization operator
(->)). The language provides richer programming constructs that were
introduced in [Lucid Synchrone](https://www.di.ens.fr/~pouzet/lucid-synchrone/index.html)
and [Scade
6](https://www.college-de-france.fr/media/gerard-berry/UPL9185028255611736393_BP_CollegeDeFrance_23_avril_2013.pdf):
by-case definitions of streams and pattern matching; an operator
"last" which refers to the previous value of a stream, hierarchical
automata and array operations. Functions can take as argument values
that can be specified to be statically known, at compile-time or
instanciation time. The language provides a more experimental features
like higher-order an functional recursion parameterized by a size.

The goal of this prototype is to define a reference executable
semantics. Its first intension is to be used independently of a
compiler to serve as an oracle for compiler testing. It serves to specify what
are the correctness properties on the various dedicated type systems
done by the compiler, that is, that a well typed/causal/clocked/initialized
program does not lead to an error; to
prove semantics preservation of source-to-source transformations
performed by the compiler (static scheduling or the compilation of automata, etc.).

The ZRun interpreter makes no a priori hypothesis on typing and other
type-based static analyses performed by a synchronous language
compiler. Hence, ZRun can execute "unfinished programs" or programs that are
semantically correct but are statically rejected by the compiler.

ZRun illustrates key differences in the treatment of
causality between Lustre, Lucid Synchrone/Scade/Zelus and Esterel. Those
differences can be observed on the same program with a simple
command-line option (-lustre and -esterel). Lustre is the most restrictive in term of
feed-back loops while Esterel is the most permissive; the languages Lucid Synchrone, Scade 6 and Zelus are
in between, with a particular treatment of by-case definitions of streams.

Finally, being independent of a compiler, this semantics
can be used to prototype new language constructs before considering
their compilation.

The long term objective is to define an executable semantics that deal
with all the language features of Zélus. For the moment, 
"hybrid" nodes where continuous-time signals are defined by Ordinary
Differential Equations (ODEs) and zero-crossing events are
not treated.

ZRun was inspired by several works. The PhD. thesis of Gonthier 1/
"Sémantiques et modèles d'exécution des langages réactifs synchrones :
application à Esterel", 1988; 2/ "The Constructive Semantics of Pure
Esterel (Draft Version 3), by Berry; 3/ "The semantics and execution
of a synchronous block-diagram language", by Edwards and Lee, Science
of Computer Programming 2003. 4/ "A Coiterative Characterization of
Synchronous Stream Functions", by Caspi and Pouzet, CMCS, 1998
(VERIMAG tech. report, 1997); All are based on the fix-point
computation of a monotone function on a domain with bounded height
that is done at every reaction. The present work builds directly on
4/, reformulating the semantics so that it can be implemented in a
statically typed, call-by-value and purely functional language that
has strong normalization property (e.g., the programming language of
Coq). In comparison, the original version in 4/ was a shallow
embedding in a language with call-by-need (precisely Haskell). You can
read the companion paper "[A Constructive State-based Semantics and
Interpreter for a Synchronous Data-flow Language with State
machines](https://www.di.ens.fr/~pouzet/bib/emsoft23b-extended.pdf)"
presented at EMSOFT'2023.

If you find this work useful for your own work, please cite this paper.
The implementation was a lot of work! If you have any
comment or question, please send a mail to Marc.Pouzet@ens.fr.

## Getting Started

The interpreter is written in OCaml mostly in purely functional style.
The simplest way to install the dependencies is via [OPAM](https://opam.ocaml.org/).

```bash
opam install dune menhir alcotest
```

Then to build the interpreter:

```bash
make
```

This will generate a `zrun.exe` executable.

```bash
 ./zrun.exe --help
Options are:
 -s            The main node to evaluate
  -all          Evaluate all nodes
  -n            The number of steps
  -v            Verbose mode
  -vv           Set even more verbose mode
  -debug        Set debug mode
  -print        Print values
  -noassert     No check of assertions
  -nocausality  Turn off the check that are variables are non bottom
  -fix          Print the number of steps for fixpoints
  -esterel      Sets the interpretation of if/then/else to be constructive
  -lustre       Sets the interpretation of if/then/else to be strict 
		(that of Lustre)
  -help         Display this list of options
  --help        Display this list of options
```

## Examples

Examples are located in the `tests` directory.

Consider for instance a simple program that computes two mutually recursive
definitions of the sinus and cosinus (`tests/good/sin_cos.zls`).

```ocaml
(* sinus/cosinus *)
(* file sin_cos.zls *)

(* forward Euler *)
let node euler_forward(h, x0, xprime) returns (x)
  x = x0 -> pre(x +. h *. xprime)

(* Backward Euler *)
let node euler_backward(h, x0, xprime) returns (x)
    x = x0 -> pre(x) +. h *. xprime

let h = 0.1
    
(* Computation of the sinus and cosinus signals *)
(* Note that the two equations defining [sin] and [cos] *)
(* are causal but they are not syntactically causal. *)
(* [euler_forward(h, 0.0, cos)] does not instantaneously depends on [cos] *)
(* but, in order to generate statically scheduled sequential code, the *)
(* compiler (of Lustre, Scade and Zelus) inline the functional call. *)

(* Note that this program executes with zrun with no deadlock *)
let node sin_cos() returns (sin, cos)
  do sin = euler_forward(h, 0.0, cos)
  and cos = euler_backward(h, 1.0, -. sin) done

let b = 0.1

let node main() returns
    (sin_val, sin_ref, cos_val, cos_ref, diff_sin, diff_cos)
  local time
  do (sin_val, cos_val) = sin_cos()
  and sin_ref = sin time
  and cos_ref = cos time
  and time = 0.0 -> pre time +. h
  and diff_sin = abs_float (sin_val -. sin_ref)
  and diff_cos = abs_float (cos_val -. cos_ref)
  and assert (diff_sin <= b) && (diff_cos <= b)
  done
```

To run this program for 1000 steps, 
type:

```
./zrun.exe -s main -n 1000 tests/good/sin_cos.zls
```
	
We now consider a more example with nested hierarchical automata
as introduced in Lucid Synchrone and Scade 6. For
example, the simple chronometer in `tests/good/chrono_in_scade.zls` 
(we use small constants in the counters to speedup the outputs).

```ocaml
(*
file watch_in_scade.zls
This example is adapted from a classical example from Scade

-------------------------- Watch Interface-------------------------
-- stst : start/stop button
-- rst : reset button
-- set : set time button
-- md : mode selection button
-- a1, a2, a3 : time data display
-- l_ : is displaying lap time
-- s_ : is in setting time mode
-- sh_ : is in setting hour mode
-- s_ and not sh_ : is in setting minutes mode
-------------------------------------------------------------------
 *)

let node root (stst,rst,set,md) returns (a1, a2, a3, l_, s_, sh_ )
local
  isStart default false, (* -- is the chrono started? *)
  is_w default false, (* -- is watch in clock mode? *)
  sigS default false,
  sigSh default false,
  sigL default false,
  m init 0, s init 0, d init 0, (* -- chrono timers *)
  last wh, last wm, last ws, last w (* -- clock timers *)
do
  l_ =  sigL
and
  s_ =  sigS
and
  sh_ =  sigSh
and
  automaton (* -- Chrono ----------------------*)
  | Stop ->
      do
	m, s, d = (0, 0, 0) -> (last m, last s, last d)
      unless
        (stst && not is_w) continue Start
      else (rst && not (false -> pre l_) && not is_w) then Stop
  | Start ->
      do
        d = (last d + 1) mod 100
      and
	s = (if (d < last d) then last s + 1 else last s) mod 60
      and
	m = if (s < last s) then last m + 1 else last m
      and
	isStart = true
      unless (stst && not is_w) continue Stop
  end
and
  automaton (* -- Watch ------------------*)
  | Count ->
      do
        wm = 0 -> (if (ws < last ws)
	           then last wm + 1 else last wm) mod 60
      and
	wh = 0 -> (if (wm < last wm)
	           then last wh + 1 else last wh) mod 24
      until (set && is_w) then Set
  | Set -> (* -- Set time *)
      local synchro default false
      do
        sigS = true
      and
        automaton (* -- set Watch -----------*)
        | Set_hr -> (* -- set hour first *)
            do
              sigSh = true
	    and
              wh = (if stst then last wh + 1
                    else if rst then last wh +23
                    else last wh) mod 24
	    until set then Set_mn
        | Set_mn -> (* -- then set minutes *)
            do
              wm = (if stst then last wm + 1
                    else if rst then last wm +59
                    else last wm) mod 60
	    until set then Set_end
        | Set_end -> do synchro = true done
	end
      until synchro continue Count
  end
and
    w = 0 -> (pre w + 1) mod 100
and
    ws = 0 -> (if (w < pre w) then pre ws + 1 else pre ws) mod 60
and  
  automaton (* -- Display ----------------*)
  | DispClk -> (* -- display watch *)
    do
      is_w = true
    and
      a1, a2, a3 = (wh, wm, ws)
    unless (md && not s_) continue DispChr
  | DispChr ->(* -- display chrono *)
    local
	lm init 0, ls init 0, ld init 0
	(* -- chrono display (to deal with lap time) *)
    do
        a1, a2, a3 = (lm, ls, ld)
    and
	automaton (* -- deal with lap time and current time ---*)
	| DispTime ->
            do
              lm, ls, ld = (m, s, d)
            unless (rst && isStart) then DispLap
	| DispLap ->
            do
              sigL = true
	    unless (rst) then DispTime
        end
    unless md continue DispClk
  end
done

let node counter(n) returns (ok)
  local c
  do
      c = 0 -> (pre c + 1) mod n
  and
      ok = (c = 0)
  done
      
let node main () returns (a1, a2, a3, l, s, sh)
  local stst, rst, set, md
  do
      stst = counter(5)
  and
      rst = counter(10)
  and
      set = counter(20)
  and
      md = counter(30)
  and
      (a1, a2, a3, l, s, sh) = root (stst, rst, set, md)
  done
      
```

The file `tests/goog/watch_in_scade.zls` also contains a `main` node to simulate one possible execution.
To run this example for 30 steps:

```bash
./zrun.exe -s main -n 30 tests/good/watch_in_scade.zls
```

A program is dynamically causally correct is all signals are non
bottom values. The following is a classical example of a program that
is dynamically causal in Esterel but not in Lustre. It is used as an
example to illustrate the fixpoint semantics presented in the paper:
"The semantics and execution of a synchronous block-diagram language",
Stephen Edwards and Edward Lee, SCP'2003. This example is due to
Robert de Simone and cited by Gerard Berry in the Esterel
primer V5.91 of 2000. The data-flow representation given below is
adapted from that of SCP'2003 paper.

```ocaml
(* file arbiter.zls *)

let node or_gate(x,y) returns (z)
    z = x || y

let node and_gate(x,y) returns (z)
    z = x && y

let node arbiter(i, request, pass_in, token_in) returns (grant, pass_out, token_out)
  local o
  do
    grant = and_gate(request, o) (* 1 *)
  and
    pass_out = and_gate(not request, o)  (* 2 *)
  and
    o = or_gate(token_in, pass_in) (* 3 *)
  and
    token_out = i fby token_in
  done
      
let node arbiter_three(i, request1, request2, request3) returns (grant1, grant2, grant3)
  local pass_out1,
        pass_out2,
        pass_out3,
        token_out1,
        token_out2,
        token_out3
  (* the following set of equations is cyclic if we build an
  unconditional dependence graph *)
  do
    grant1, pass_out1, token_out1 = arbiter(request1, pass_out3, token_out3)
  and
    grant2, pass_out2, token_out2 = arbiter(request2, pass_out1, token_out1)
  and
    grant3, pass_out3, token_out3 = arbiter(request3, pass_out2, token_out2)
  done

let node main() returns (grant1, grant2, grant3) local request1,
  request2, request3 do request1 = true and request2 = true and
  request3 = true and grant1, grant2, grant3 = arbiter_three(request1,
  request2, request3) 
done 
``` 

Depending on the way the `or` and `and` operator are defined, outputs
of `main()` are either bottom or not. By default, Zrun considers that
all imported primitives (here `||` and `&&`) are strict
(output is bottom whenever one input is bottom). Hence, typing:

`zrun.exec -s main -n 10 arbiter.zls`

returns a sequence of bottom values for all ouptuts. The program is
not causally correct. Defining:

```ocaml
(* the two boolean operators below are sequential, not symetric as *)
(* in Esterel and the SCP'2003 paper. In the current semantics all imported *)
(* functions are strict, hence preventing *)
(* to have or(true, x) = or(x, true) = true whenever x is bot *)
let node or_gate(x,y) returns (z)
    z = if x then true else y y

let node and_gate(x,y) returns (z)
    z = if x then y else false
```
leads to a program that is causally correct. Here, the operators
are only strict in their first argument. Note that the arbiter
example is causally correct if
the two boolean operators of lines (1) and (2) are strict but
the one on line (3) is sequential (left-to-right). If the order
of arguments in line (3) is reversed, that is:

or_gate(pass_in, token_in)

the program is no more causally correct. To recover the expressiveness of
Esterel (and the SCP'2003 paper), type:

`zrun.exec -esterel -s main -n 10 arbiter.zls`

the program is now causally correct. The interpreter provides three different
interpretation of the conditional `if/then/else` that can be choosen
on the command line.

To see simple examples that illustrate the treatment of causality
  between Lustre on one side, Lucid Synchrone/Scade/Zelus that sits in between
  and Esterel as the most expressive, see file
  `tests/good/lustre_versus_lucid_synchrone_versus_esterel.zls`. See
  other examples in directory tests/

## Citing Zrun

```
@InProceedings{lucy:emsoft23b,
  author = 	 {Jean-Louis Colaco and
                  Michael Mendler and
		  Baptiste Pauget and
		  Marc Pouzet},
  title = 	 {{A Constructive State-based Semantics and Interpreter for a Synchronous Data-flow Language with State machines}},
  booktitle = {International Conference on Embedded Software (EMSOFT'23)},
  year = 	 2023,
  month = 	 {September 17-22},
  address = 	 {Hamburg, Germany},
  organization = {ACM}}
```
