all: build tests

build:
	(cd src/zrun; dune build -- zrun.exe)

buildv:
	(cd src/zrun; dune build --verbose -- zrun.exe)

tests:
	(cd tests; dune test)

debug:
	(cd src/zrun; dune build --debug-backtraces --debug-dependency-path -- zrun.bc)

clean:
	dune clean;
	(cd tests/good/; rm -f *.zlo);
	(cd tests/bad/; rm -f *.zlo)

wc:
	(cd src; wc global/*.ml \
	parsing/parsetree.ml parsing/*.mll \
	zrun/*.ml)

.PHONY: build buildv tests debug clean wc
