# Qunity

This repository contains Coq proofs and code associated with the
POPL 2023 paper
["Qunity: A Unified Language for Quantum and Classical Computing"](https://doi.org/10.1145/3571225),
by [Finn Voichick](https://orcid.org/0000-0002-1913-4178),
[Liyi Li](https://orcid.org/0000-0001-8184-0244),
[Robert Rand](https://orcid.org/0000-0001-6842-5505), and
[Michael Hicks](https://orcid.org/0000-0002-2759-9223). The code in this
repository was written by Finn and Liyi, supervised by Robert and Mike, with
some advice from [Leonidas Lampropoulos](https://orcid.org/0000-0003-0269-9815).
It is available online at
[gitlab.umiacs.umd.edu/finn/qunity](https://gitlab.umiacs.umd.edu/finn/qunity)
and [doi:10.5281/zenodo.7150282](https://doi.org/10.5281/zenodo.7150282)

The Coq code in this repository formally defines the Qunity language, including
a typechecker. The soundness of the typechecker has been formally verified.
Compilation is a work in progress.

## Getting Started 

This repository includes the code associated with our paper. With Coq installed,
you should be able to compile everything by running `make` in the project root.
We have tested this code using Coq 8.15.

## Contents

This repository contains the following files in the `src` directory:

### Basic utilities for proof engineering
- `Tactics.v`: Widely used tactics and lemmas, including those involving
  decidable equality.
- `Lists.v`: General functions and lemmas related to Coq lists
- `Sets.v`: Specialized definitions using lists of strings to manipulate
  unordered sets of variables.

### Language definitions
- `Types.v`: Algebraic data types in Qunity
- `Syntax.v`: Qunity language and related notations
- `Contexts.v`: Typing contexts mapping variables to types, represented as lists
  of pairs
- `Typing.v`: Qunity's typing relations
- `Typechecking.v`: A type inference algorithm

### Examples
- `examples/QList.v`: Fixed-length quantum arrays
- `examples/Deutsch.v`: Deutsch's algorithm
- `examples/DeutschJozsa.v`: The Deutsch-Jozsa algorithm
- `examples/Fourier.v`: The quantum Fourier transform
- `examples/Walk.v`: The quantum walk described in our paper

## Legal

Qunity is free software: you can redistribute it and/or modify it under the
terms of the [GNU General Public License](LICENSE.md) as published by the Free
Software Foundation, either version 3 of the License, or (at your option) any
later version.
