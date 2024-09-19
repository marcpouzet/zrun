all:
	dune build -- zrun.exe
	dune build -- zwrite.exe
	dune build -- zeluc.exe

debug:
	dune build --debug-backtraces --debug-dependency-path -- zrun.bc
	dune build --debug-backtraces --debug-dependency-path -- zwrite.bc
	dune build --debug-backtraces --debug-dependency-path -- zeluc.bc

clean:
	dune clean

