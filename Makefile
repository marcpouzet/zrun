all: build tests

build:
	(cd src; dune build -- zrun.exe)

tests:
	(cd tests; dune test)

debug:
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zrun.bc)

clean:
	dune clean

wc:
	wc global/*.ml \
	parsing/parsetree.ml parsing/*.mll compiler/parsing/*.mly \
	zrun/*.ml

