(lang dune 3.0)
(using menhir 2.0)
(wrapped_executables false)
(generate_opam_files true)

(name zrun)
(version z0)
(authors "Marc Pouzet <marc.pouzet@ens.fr>")
(maintainers "Marc Pouzet <marc.pouzet@ens.fr>")
(source (github marcpouzet/zrun))

(package
 (name zrun)
 (synopsis "ZRun, A synchronous language interpreter")
 (description "Executable reference semantics for the Zelus synchronous data-flow language, limited to discrete time.")
 (depends
  (ocaml (>= 5.1))
  dune
  (menhir :build)
  (alcotest :with-test)))
