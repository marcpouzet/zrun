all: zrun.exe zwrite.exe zeluc.exe

zrun.exe:
	(cd src; dune build -- zrun.exe)

zwrite.exe:
	(cd src; dune build -- zwrite.exe)

zeluc.exe:
	(cd src; dune build -- zeluc.exe)

zrun.exe.verbose:
	(cd src; dune build --verbose -- zrun.exe)

tests:
	(cd tests; dune test)

debug:
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zrun.bc)
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zwrite.bc)
	(cd src; dune build --debug-backtraces --debug-dependency-path -- zeluc.bc)

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
	compiler/typing/*.ml \
	compiler/analysis/*.ml \
	compiler/gencode/*.ml \
	compiler/main/*.ml)

.PHONY: zeluc.exe zeluc.exe zrun.exe zwrite.exe zrun.exe.verbose tests debug clean wc
