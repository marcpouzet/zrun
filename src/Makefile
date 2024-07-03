all:
	dune build -- zrun.exe
	dune build -- zwrite.exe

debug:
	dune build --debug-backtraces --debug-dependency-path -- zrun.bc
	dune build --debug-backtraces --debug-dependency-path -- zwrite.bc

clean:
	dune clean

