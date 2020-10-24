# The ZRun Interpreter

ZRun is an interpreter for a synchronous data-flow language which allows
for mixing data-flow equations (a la Lustre) and hierarchical automata (a la
Lucid Synchrone).

The purpose of this prototype is to give a reference and executable semantics for a
language like Scade that can be used 1/ for compiler testing; 2/ to prove
compilation steps (e.g., that a well typed program does not lead to a
type error; or source-to-source transformations like static scheduling
or the compilation of automata); 3/ to execute unfinished
programs or programs that are possibly cyclic and accepted by an Esterel
compiler (the so-called "constructively causal" programs) but rejected
by Lustre, Lucid Synchrone, Scade, Zelus that impose stronger causality
constraints; 4/ to prototype new language constructs for synchronous languages.

The long term objective is to address all Zelus (we are far from
that! for the moment, the input language lacks higher-order,
arrays and is purely discrete-time). Moreover, there is no static checks!

The language kernel is a subset of Zelus (and Lucid Synchrone). In particular,
state automata can be parameterized. Paper [EMSOFT'05] defines a semantics
by translation into a small data-flow kernel from an input language that is
very close to what zrun executes; [EMSOFT'06] defines a relational semantics. Here,
the semantics is denotational and executable following what paper
"The semantics and execution of a synchronous block-diagram language",
Edwards and Lee, Science of Computer Programming 2006.

The internal mechanics of the semantics and interpreter is based on
(an old) paper "A Coiterative Characterization of Synchronous Stream
Functions", by Caspi and Pouzet, CMCS, 1998 (VERIMAG tech. report,
1997).

If you find this work useful or have any comment/criticism,
please send a mail to Marc.Pouzet@ens.fr.


## Getting Started

The interpreter is written in OCaml.
The simplest way to install the dependencies is via [OPAM](https://opam.ocaml.org/).

```bash
opam install dune menhir
```

Then to build the interpreter:

```bash
make
```

This will generate a `zrun.exe` executable.

```bash
 ./zrun.exe --help
Options are:
  -s         The main node to evaluate
  -n         The number of steps
  -check     Check that the simulated node returns true
  -v         Verbose mode
  -noassert  No check of assertions
  -help      Display this list of options
  --help     Display this list of options
```

## Examples

Examples are located in the `tests` directory.
Consider for instance the simple chronometer in `tests/chrono_in_scade.zls` 
(we use small constants in the counters to speedup the outputs).

```
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

The file `tests/watch_in_scade.zls` also contains a `main` node to simulate one possible execution.
To run this example for 30 steps:

```bash
./zrun.exe -s main -n 30 tests/watch_in_scade.zls
```

```
The following is a classical example of a cyclic program that is
statically rejected by the Lustre/Scade/Lucid Synchrone/Zelus compilers
while it is a valid Esterel program. This example is due to Robert
de Simone and is given by Berry in the Esterel primer V5.91 of 2000. It is also used as
an example to illustrate the fixpoint semantics presented in the
paper: "The semantics and execution of a synchronous block-diagram
language", Stephen Edwards and Edward Lee, SCP, 2003.

(* file arbiter.zls *)
let node and_gate(x,y) returns (z)
    if x then z = y else z = false

let node or_gate(x,y) returns (z)
    if x then z = true else z = y

let node arbiter(request, pass_in, token_in) returns (grant, pass_out, token_out)
  local o
  do
    grant = and_gate(request, o)
  and
    pass_out = and_gate(not request, o)
  and
    o = or_gate(pass_in, token_in)
  and
    token_out = false fby token_in
  done
      
let node arbiter_three(request1, request2, request3) returns (grant1, grant2, grant3)
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

let node main() returns (grant1, grant2, grant3) 
  local request1, request2, request3
  do
    request1 = true
  and
    request2 = true
  and
    request3 = true
  and
    grant1, grant2, grant3 = arbiter_three(request1, request2, request3)
  done


See other examples in directory tests/


