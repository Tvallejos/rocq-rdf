# CoqRDF
[![Nix CI for bundle default](https://github.com/Tvallejos/rocq-rdf/actions/workflows/nix-action-default.yml/badge.svg)](https://github.com/Tvallejos/rocq-rdf/actions/workflows/nix-action-default.yml)

Development of the RDF model using Coq and the Mathematical Components library.

## Meta

- Author(s):
  - Tomas Vallejos
  - Assia Mahboubi
- Compatible Rocq versions: 9.0.0
- Additional dependencies: 
  - the [`Mathematical Components` Library](https://github.com/math-comp/math-comp) version 2.3.0
  
## Description

This library allows mechanized reasoning about the RDF model. 
It defines RDF graphs as duplicate-free sequences of triples; and operations on them, such as, blank node relabeling and RDF isomorphism.

## Installation

We recommend installing the dependencies via [OPAM](https://opam.ocaml.org/doc/Install.html) (using a fresh or up to date version of opam 2), and then build manually:

```sh
git clone https://github.com/Tvallejos/rocq-rdf.git
cd rocq-rdf
opam switch create rocq-rdf 4.12.0
eval $(opam env)
opam remote add coq-released https://rocq-prover.org/opam/released
opam install .
```

