all:
	dune build -- zrun.exe

debug:
	dune build --debug-backtraces --debug-dependency-path -- zrun.bc

clean:
	dune clean

wc:
	wc global/*.ml \
	parsing/parsetree.ml parsing/*.mll compiler/parsing/*.mly \
	zrun/*.ml

