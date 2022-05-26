# k

This repository contains the artifact accompanying the paper
*Normalization for Fitch-style Modal Calculi*.

## Dependencies

- [Agda](https://agda.readthedocs.io/en/v2.6.2.1/) version 2.6.2.1
- [Agda standard library](https://github.com/agda/agda-stdlib/) version 1.7.1

## Check

To typecheck the code, run the following command line from the
repository directory:

> agda src/Everything.agda

## Contents

The repository contains the mechanization of the normalization
function for the calculi $λ_\text{IK}$ (`src/IK/`) and $λ_\text{IS4}$
(`src/IS4/`) as described in the paper.

### Pointers from the paper to the code

+ Section 3

  - Type syntax -> `src/IK/Type.agda`
  - Context syntax and order-preserving embeddings (OPEs) -> `src/Context.agda`

+ Section 3.1 ($λ_\text{IK}$)

  - Section 3.1.1
    + Modal accessibility relation (Fig. 4) -> `src/Context.agda`
    + Substitutions (Fig. 6) -> `src/Context.agda`
    + Intrinsically typed syntax (Fig. 5), weakening and substitution -> `src/IK/Term.agda`
    + Equational theory (Fig. 7) -> `src/IK/Conversion.agda`

  - Section 3.1.2
    + Evaluation function `eval` -> `src/IK/Norm.agda`
    + Soundness of evaluation (Theorem 2) -> `src/IK/Soundness/`

  - Section 3.1.3
    + Normal and neutral forms (Fig 7.) -> `src/IK/Norm.agda`
    + `reify` and `reflect` -> `src/IK/Norm.agda`
    + `quote` and identity environment `freshEnv` (***FIXME called `id_s` in the code***) -> `src/IK/Norm.agda`
    + Logical relation (Fig. 9) and fundamental theorem (Proposition 3) -> `src/IK/Completeness/`
    + Completeness and adequacy of normalization (Theorem 4) -> ***FIXME***

+ Section 3.2 ($λ_\text{IS4}$)

  - Section 3.2.1
    + Modal accessibility relation (Fig. 10) -> `src/Context.agda`
    + Substitutions (Fig. 11.) -> `src/Context.agda`
    + Intrinsically typed syntax (Fig. 11), weakening and substitution -> `src/IS4/Term.agda`
    + Equational theory (Fig. 12) -> `src/IS4/Conversion.agda`

  - Section 3.2.2
    + Evaluation function -> ***FIXME***
    + Soundness of evaluation (Theorem 6) -> ***FIXME***

  - Section 3.2.3
    + Normal and neutral forms -> `src/IS4/Norm.agda`
    + `reify` and `reflect` -> `src/IS4/Norm.agda`
    + Completeness and adequacy of normalization (Theorem 7) -> ***FIXME***