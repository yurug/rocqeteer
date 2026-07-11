(lang dune 3.23)
(using rocq 0.13)
(name rocqeteer)
(generate_opam_files true)
(source (github yurug/rocqeteer))
(authors "Yann Régis-Gianas")
(maintainers "yann.regis-gianas@nomadic-labs.com")
(package
 (name rocqeteer)
 (synopsis
  "Use Rocq as a certified programming language: prove effectful programs, run them as fast idiomatic OCaml 5")
 (description
  "Domain-independent trusted toolchain: write effectful programs in a first-order IR in Rocq, prove them against reference semantics, and lower them to direct-style OCaml 5 with effect handlers. Installs the Rocqeteer Rocq theory and the rocqeteer-codegen CLI. Requires a Rocq 9.1 toolchain in the same switch.")
 (depends (ocaml (>= 5.4)) dune zarith base-unix))
