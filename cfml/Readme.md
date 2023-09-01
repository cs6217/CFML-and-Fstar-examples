# Verifying OCaml Code with CFML

This project consists of a series of examples of verifying OCaml code in Coq.

Once you have installed the requirements, build the programs and their proofs with dune:
```
opam exec -- dune build @all
```

## Requirements

- Coq == 8.14.1
- Coq-Cfml >= 20220112
- OCaml 4.12.0

Once you have the coq-repositories added:

```
opam repo add coq-released https://coq.inria.fr/opam/released
```

Simply install cfml:
```
opam install cfml coq-cfml
```

## Project Structure

```
.
├── lib                OCaml code
├── proofs             Coq proofs 
├── dune-project
└── Readme.md


3 directories, 2 files
```

