all: build tests

build:
	(cd src; dune build -- zrun.exe)

tests:
	(cd tests; dune test)

debug:
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zrun.bc)

clean:
	dune clean;
	(cd tests/good/; rm -f *.zlo);
	(cd tests/bad/; rm -f *.zlo)

wc:
	(cd src; wc global/*.ml \
	parsing/parsetree.ml parsing/*.mll \
	zrun/*.ml)

