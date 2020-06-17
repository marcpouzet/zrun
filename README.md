# The ZRun Interpreter

ZRun is an interpreter for a synchronous data-flow language where data-flow equations and hierarchical automata can be arbitrarily nested.


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
Consider for instance the simple chronometer in `tests/chrono.zls` 
(we use small constants in the counters to speedup the outputs).

```
let node chrono (stst, rst)
  returns (s init 0, m init 0)
  reset
      automaton
        | STOP ->
            do
            unless stst continue START
        | START -> local d
            do d = count_mod 2
            and if edge (d = 0) then s = count_mod 3
            and if edge (s = 0) then m = count_mod 5
            unless stst continue STOP
      end
  every rst
```

The file `tests/chrono.zls` also contains a `main` node to simulate one possible execution.
To run this example for 30 steps:

```bash
./zrun.exe -s main -n 30 tests/chrono.zls
```




