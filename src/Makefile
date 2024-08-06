all:
	(cd zrun; dune build -- zrun.exe)
	(cd compiler/main; dune build -- zwrite.exe)

debug:
	(cd zrun; dune build --debug-backtraces --debug-dependency-path -- zrun.bc)
	(cd compiler/main; dune build --debug-backtraces --debug-dependency-path -- zwrite.bc)

clean:
	dune clean

