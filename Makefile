all:
	dune build src/zrun.exe

debug:
	dune build --debug-backtraces --debug-dependency-path src/zrun.bc

clean:
	dune clean; rm -f *~
