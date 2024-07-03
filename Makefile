all: zrun.exe zwrite.exe

zrun.exe:
	(cd src; dune build -- zrun.exe)

zwrite.exe:
	(cd src; dune build -- zwrite.exe)

zrun.exe.verbose:
	(cd src; dune build --verbose -- zrun.exe)

tests:
	(cd tests; dune test)

debug:
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zrun.bc)
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zwrite.bc)

clean:
	dune clean;
	(cd tests/good/; rm -f *.zlo);
	(cd tests/bad/; rm -f *.zlo)

wc:
	(cd src; wc global/*.ml \
	parsing/parsetree.ml parsing/*.mll \
	zrun/*.ml \
	compiler/tydefs/*.ml \
	compiler/rewrite/*.ml \
	compiler/main/*.ml)

.PHONY: zrun.exe zwrite.exe zrun.exe.verbose tests debug clean wc
