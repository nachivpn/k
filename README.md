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

### Assumptions

The code/proofs depend on the following axioms:
  + `K`
  + Function extensionality

We note that function extensionality is not strictly required; it
helps simplify the proof of soundness for the evaluation function of
$λ_\text{IK}$.

## Contents

The repository contains the mechanization of the normalization
function for the calculi $λ_\text{IK}$ (`src/IK/`) and $λ_\text{IS4}$
(`src/IS4/`) as described in the paper.

### Pointers from the paper to the code

+ Section 3

  - Type syntax → `src/IK/Type.agda`
  - Context syntax → lines 25--28 in `src/Context.agda` 
  - Order-preserving embeddings (OPEs) (Fig. 3) → lines 72--76 in `src/Context.agda`

+ Section 3.1 ($λ_\text{IK}$)

  - Section 3.1.1
    + Modal accessibility relation (Fig. 4) → lines 218--219 in `src/Context.agda`
    + Substitutions (Fig. 6) → lines 720--723 in `src/Context.agda`
    + Intrinsically typed syntax (Fig. 5), weakening and substitution → `src/IK/Term/Base.agda`
    + Equational theory (Fig. 7) → `src/IK/Conversion.agda`

  - Section 3.1.2
    + Evaluation function → function `eval` in lines 74--79 of `src/IK/Norm/NbE/Model.agda`
    + Soundness of evaluation (Theorem 2) → lines 329--339 in `src/IK/Norm/Properties/Completeness/Completeness.agda`

  - Section 3.1.3
    + Normal and neutral forms (Fig 8.) → datatypes `Nf` and `Ne` in `src/IK/Term/NormalForm/Base.agda`
    + `reify` and `reflect` → `src/IK/Norm/NbE/Reification.agda`
    + `quote` and identity environment `freshEnv` (***called `id_s` in the code***) → `src/IK/Norm/Base.agda` and `src/IK/Norm/NbE/Reification.agda`
    + Logical relation (Fig. 9) and fundamental theorem (Proposition 3) → `src/IK/Norm/Properties/Soundness/Trace.agda`
    + Completeness and adequacy of normalization (Theorem 4) → Completeness is called `norm-complete` in lines 377--378 of `src/IK/Norm/Properties/Completeness/Completeness.agda` and adecuacy is called `norm-sound` in lines 31--36 of `src/IK/Norm/Properties/Soundness/Soundness.agda`

+ Section 3.2 ($λ_\text{IS4}$)

  - Section 3.2.1
    + Modal accessibility relation (Fig. 10) → lines 222--223 in `src/Context.agda`
    + Substitutions (Fig. 11.) → lines 720--723 in `src/Context.agda`
    + Intrinsically typed syntax (Fig. 11), weakening and substitution → `src/IS4/Term.agda`
    + Equational theory (Fig. 12) → `src/IS4/Conversion.agda`

  - Section 3.2.2
    + Evaluation function → `src/Semantics/Clouston/Evaluation/IS4.agda`
    + Soundness of evaluation (Theorem 6) → lines 584--587 in `src/Semantics/Clouston/Evaluation/IS4/Properties.agda`

  - Section 3.2.3
    + Normal and neutral forms → datatypes `Nf` and `Ne` in `src/IS4/Term/NormalForm/Base.agda`
    + `reify` and `reflect` → `src/IS4/Norm/NbE/Reification.agda`
    + Completeness and adequacy of normalization (Theorem 7) → Completeness is called `norm-complete` in `src/IS4/Norm/Properties/Completeness.agda` and adecuacy is called `norm-sound` in lines 297--298 of `src/IS4/Norm/Properties/Soundness.agda`