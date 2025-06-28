# Logical Relations for Formally Verified Authenticated Data Structures

This repository contains the Rocq and OCaml development accompanying the CCS 2025 submission *Logical Relations for Formally Verified Authenticated Data Structures* by Simon Oddershede Gregersen, Chaitanya Agarwal, and Joseph Tassarotti.

A high-level overview of the repository and build instructions are found below. [PAPER.md](PAPER.md) provides a detailed mapping from the paper to the OCaml and Rocq developments.

The design of the `Authentikit` OCaml library is due to [Bob Atkey](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html).
Our approach to (type) binding found in [theories/binding](theories/binding) is due to [Filip Sieczkowski and Piotr Polesiuk](https://popl24.sigplan.org/details/CoqPL-2024-papers/7/Functorial-Syntax-for-All).

## Overview

Below is an overview of the most relevant folders and files. 

- [theories/](theories/): Rocq development
  + [examples/](theories/examples/)
    - [authentikit.v](theories/examples/authentikit.v): the Authentikit interface
    - [authentikit_base_security.v](theories/examples/authentikit_base_security.v): shared aux. results and definitions for the security proofs.
    - [authentikit_base_correctness.v](theories/examples/authentikit_base_security.v): shared aux. results and definitions for the correctness proofs.
    - [authentikit_list.v](theories/examples/authentikit_list.v): naive Authentikit implementation
    - [authentikit_list_security.v](theories/examples/authentikit_list_security.v): security of the naive Authentikit implementation
    - [authentikit_list_correctness.v](theories/examples/authentikit_list_correctness.v): correctness of the naive Authentikit implementation 
    - [authentikit_rev_list.v](theories/examples/authentikit_rev_list.v): list-reverse optimization
    - [authentikit_rev_list_correctness.v](theories/examples/authentikit_rev_list_correctness.v): correctness
    - [authentikit_buf.v](theories/examples/authentikit_buf.v): proof-buffering optimization
    - [authentikit_buf_security.v](theories/examples/authentikit_buf_security.v): security
    - [authentikit_buf_correctness.v](theories/examples/authentikit_buf_correctness.v): correctness
    - [authentikit_buf_magic.v](theories/examples/authentikit_buf_magic.v): proof buffering and hetereogenous cache optimization
    - [authentikit_buf_magic_security.v](theories/examples/authentikit_buf_magic.v): security
    - [authentikit_buf_magic_correctness.v](theories/examples/authentikit_buf_magic.v): correctness
    - [authentikit_buf_magic_state.v](theories/examples/authentikit_buf_magic_state.v): stateful optimization
    - [authentikit_buf_magic_state_security.v](theories/examples/authentikit_buf_magic_state.v): security
    - [authentikit_buf_magic_state_correctness.v](theories/examples/authentikit_buf_magic_state.v): correctness
    - [pair.v](theories/examples/pair.v): minimal example of manual security/correctness proof
    - [merkle.v](theories/examples/merkle.v): optimized Merkle retrieve, implementation
    - [merkle_retrieve_security.v](theories/examples/merkle_retrieve_security.v): security
    - [merkle_retrieve_correctness.v](theories/examples/merkle_retrieve_correctness.v): correctness
  + [heap_lang/](theories/heap_lang):
    - [lang.v](theories/heap_lang/lang.v): the definition of untyped $F_{\omega, \mu}^{ref}$
    - [adequacy_upto_bad.v](theories/heap_lang/adequacy.v): soundness of CF-SL
  + [program_logic_upto_bad/](theories/program_logic_upto_bad/): generic up-to-bad logic, specialized to obtain CF-SL
  + [rel_logic_bin/](theories/rel_logic_bin/): binary logical relation
  + [rel_logic_tern/](theories/rel_logic_tern/): ternary logical relation
  + [typing/](theories/typing/): types and syntactic type system for $F_{\omega, \mu}^{ref}$
- [src/](src/): OCaml development
  + [basic/](src/basic): this matches the Rocq development
    - [auth.ml](src/basic/auth.ml): the Authentikit interface
    - [authenticatable_base.ml](src/basic/authenticatable_base.ml): serialization/deserialization library
    - [prover.ml](src/basic/prover.ml): prover's naive Authentikit implementation
    - [prover_rev.ml](src/basic/prover_rev.ml): prover's list-reverse optimization
    - [prover_buf.ml](src/basic/prover_buf.ml): prover's proof-buffering optimization
    - [prover_buf_magic_state.ml](src/basic/prover_buf_magic_state.ml): prover's stateful optimization
    - [verifier.ml](src/basic/verifier.ml): verifier's naive Authentikit implementation
    - [verifier_buf.ml](src/basic/verifier_buf.ml): verifier's proof-buffer optimization
    - [verifier_buf_magic.ml](src/basic/verifier_buf_magic.ml): verifier's heterogenous-caching optimization
    - [verifier_buf_magic_state.ml](src/basic/verifier_buf_magic_state.ml): verifier's stateful optimization
    - [merkle.ml](src/basic/merkle.ml): merkle tree functor that uses Authentikit and an optimized retrieve function
    - [redblack.ml](src/basic/redblack.ml): redblack functor
    - [trimerkle.ml](src/basic/trimerkle.ml): ternary rose-merkle tree functor
  + [opt/](src/opt): optimized development
    - [authenticatable_marshal.ml](src/opt/authenticatable_marshal.ml): optimized serialization library
    - [prover_rev.ml](src/opt/prover_rev.ml): prover's optimized list-reverse implementation using forced-inlining
    - [prover_io.ml](src/opt/prover_io.ml): prover's implementation that writes proof stream to a file.
    - [verifier.ml](src/opt/verifier.ml): verifier's optimized implementation using forced-inlining
    - [verifier_io.ml](src/opt/verifier_io.ml): verifier's implementation that reads proof stream from a file.

## Building the Rocq development

The project is known to compile with

- Rocq 8.19.2
- std++ 1.11.0
- Iris 4.3.0
    
The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create auth 4.14.2
opam switch link auth .
```
3. Add the Rocq `opam` repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
```
4. Install the right version of the dependencies as specified in the `auth.opam` file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Building the OCaml development

The project is known to compile with

- OCaml 4.14.2

The instructions for building the Rocq development will also install OCaml at this version. You should be able to build the development and run the test suite by running `make` in the `src/basic/` folder.

## Docker

The development can be build and run using Docker. Suggested commands for building, interacting with, saving, and loading an image are shown below. Note that building the `Dockerfile` requires the development to be available in the same folder.

### Build image

```
make tar
docker build -t auth .
```

The `build` command may need a `--platform linux/amd64` option if run on Apple Silicon.

### Interactive shell

```
docker run -i --name auth -t auth
```

### Save image

```
docker save auth:latest | gzip > docker-auth.tar.gz
```

### Load pre-built image

```
docker load < docker-auth.tar.gz
```

## Using Authentikit

We provide a few examples of authenticated data structures implemented using Authentikit: [merkle.ml](src/basic/merkle.ml), [redblack.ml](src/basic/redblack.ml), and [trimerkle.ml](src/basic/trimerkle.ml).
Further, we show the usage of the Merkle tree in [test.ml](src/basic/test.ml).

Running `make` in the `src/basic/` folder generates a binary file `test` and running `./test` will execute the test suite.
