# Normalization for Fitch-style Modal Calculi (Artifact)

This repository contains the artifact accompanying the paper
*Normalization for Fitch-style Modal Calculi*.

## Dependencies

- [Agda](https://agda.readthedocs.io/en/v2.6.2.1/) version 2.6.2.1
- [Agda standard library](https://github.com/agda/agda-stdlib/) version 1.7

## Check

To typecheck the code, run the following command line from the
repository directory:

> agda src/Everything.agda

### Assumptions

The code depends on the following two axioms:

  + Uniqueness of identity proofs (axiom K)
  + Function extensionality

Function extensionality avoids the use of setoids in the soundness
proof for the evaluation function of &lambda;<sub>IK</sub>, and axiom K allows
reasoning about values of the modal accessibility relation using
heterogeneous equality. We expect that both axioms can be dispensed
with.

## Contents

The repository contains the mechanization of the normalization
function for the calculi &lambda;<sub>IK</sub> (`src/IK/`) and &lambda;<sub>IS4</sub>
(`src/IS4/`) as described in the paper.

### Discrepancies between notation in the paper and notation in the code

|                                                | In the paper                              | In the code                    |
|------------------------------------------------|-------------------------------------------|--------------------------------|
| Lock context operator                          | `_,🔒`                                     | `_#`                          |
| Type of weakenings/order-preserving embeddings | `_≤_`                                     | `_⊆_`                          |
| Modal accessibility relations                  | `_◁IK_`, `_◁IS4_`                         | `LFExt`, `CExt` (ternary)      |
| Context extensions                             | `var`, `lock`                             | `ext`, `ext#`                  |
| Judgements                                     | `_⊢Var_`, `_⊢_`, `_⊢ₛ_`, `_⊢Ne_`, `_⊢Nf_` | `Var`, `Tm`, `Sub`, `Ne`, `Nf` |
| Equational theory                              | `_∼_`                                     | `_≈_`                          |
| Evaluation functions                           | `⟦_⟧`                                     | `Tm'`, `Sub'`, `eval`, `evalₛ` |
| Identity environment                           | `freshEnv`                                | `idₛ'`                         |

(nonexhaustive)

### Pointers from the paper to the code

+ Section 3

  - Type syntax → `src/Type.agda`
  - Context syntax → lines 31-34 in `src/Context.agda`
  - Order-preserving embeddings (OPEs) (Fig. 3) → lines 95-100 in `src/Context.agda`

+ Section 3.1 (&lambda;<sub>IK</sub>)

  - Section 3.1.1
    + Modal accessibility relation (Fig. 4) → lines 242-243 in `src/Context.agda`
    + Substitutions (Fig. 6) → lines 766-769 in `src/Context.agda`
    + Intrinsically typed syntax (Fig. 5), weakening and substitution → `src/IK/Term/Base.agda`
    + Equational theory (Fig. 7) → `src/IK/Term/Conversion.agda`

  - Section 3.1.2
    + Evaluation function → function `eval` in lines 80-85 of `src/IK/Norm/NbE/Model.agda` [1]
    + Soundness of evaluation (Theorem 2) → lines 321-331 in `src/IK/Norm/Properties/Completeness.agda`

  - Section 3.1.3
    + Normal and neutral forms (Fig 8.) → datatypes `Nf` and `Ne` in `src/IK/Term/NormalForm/Base.agda`
    + `reify` and `reflect` → `src/IK/Norm/NbE/Reification.agda`
    + `quote` and identity environment `freshEnv` (***called `id_s` in the code***) → `src/IK/Norm/Base.agda` (lines 17-18) and `src/IK/Norm/NbE/Reification.agda` (lines 29-32)
    + Logical relation (Fig. 9) and fundamental theorem (Proposition 3) → lines 27-41 and 157-194 in `src/IK/Norm/Properties/Soundness/Trace.agda`, respectively [2]
    + Completeness and adequacy of normalization (Theorem 4) → Completeness is called `norm-complete` in lines 369-370 of `src/IK/Norm/Properties/Completeness.agda` and adequacy is called `norm-sound` in lines 31-36 of `src/IK/Norm/Properties/Soundness/Soundness.agda`

+ Section 3.2 (&lambda;<sub>IS4</sub>)

  - Section 3.2.1
    + Modal accessibility relation (Fig. 10) → lines 246-247 in `src/Context.agda`
    + Substitutions (Fig. 11.) → lines 766-769 in `src/Context.agda`
    + Intrinsically typed syntax (Fig. 11), weakening and substitution → `src/IS4/Term.agda`
    + Equational theory (Fig. 12) → `src/IS4/Term/Conversion.agda`

  - Section 3.2.2
    + Evaluation function → lines 74-93 in `src/Semantics/Clouston/Evaluation/IML/Base.agda` and lines 61-81 in `src/Semantics/Clouston/Evaluation/IS4/Base.agda` (instantiated by `src/Semantics/Presheaf/Evaluation/IS4.agda`)
    + Soundness of evaluation (Theorem 6) → line 523 in `src/Semantics/Clouston/Evaluation/IS4/Properties.agda` (instantiated by `src/Semantics/Presheaf/Evaluation/IS4/Properties.agda`)

  - Section 3.2.3
    + Normal and neutral forms → datatypes `Nf` and `Ne` in `src/IS4/Term/NormalForm/Base.agda`
    + `reify` and `reflect` → `src/IS4/Norm/NbE/Reification.agda`
    + Completeness and adequacy of normalization (Theorem 7) → Completeness is called `norm-complete` in `src/IS4/Norm/Properties/Completeness.agda` and adequacy is called `norm-sound` in lines 297-298 of `src/IS4/Norm/Properties/Soundness.agda`

#### Notes:

[1]: The interpretation of types in &lambda;<sub>IK</sub> in
  lines 32-35 differs from the generic one given in Section 2 of the
  paper for the type &square;A. These are however equivalent
  interpretations in the NbE model. That is, defining ⟦ &square;A
  ⟧<sub>Γ</sub> as Γ ≤ Γ' ⇒ Γ' ◁IK Γ'' ⇒ ⟦ A ⟧<sub>Γ''</sub> is
  equivalent to defining it as ⟦ A ⟧<sub>Γ,🔒</sub>. To observe this, we
  pick Γ for Γ' and Γ,🔒 for Γ'' in one direction, and apply the
  monotonicity lemma twice in the other since Γ' ◁IK Γ'' implies Γ'' ≤
  Γ',🔒. The latter interpretation is given by the `Box` type in line
  23.

[2]: The logical relation for &lambda;<sub>IK</sub> in the
  code is actually set up so that the fundamental theorem implies the
  stronger adequacy statement `t ⟶* norm t` that terms `t` are reducible
  to their normal form `norm t` (cf. line 195). This immediately implies
  the weaker adequacy statement `t ≈ norm t` that terms `t` are
  equivalent to their normal form `norm t`. Recall that the equational
  theory `_≈_` can (and is in the code) equivalently be defined as the
  reflexive&ndash;transitive&ndash;symmetric closure of the "reduction"
  relation `_⟶_` (`_⟶*_` denotes the merely reflexive&ndash;transitive
  closure of `_⟶_`). The reduction relation is not defined in the paper
  and the logical relation for &lambda;<sub>IS4</sub> below is only set
  up to prove the weaker adequacy statement.

### Structure of the repository

The following tree gives a brief overview of the structure of the
repository with a brief description of each module.

Every path that follows is under the directory `src/`.

Modules marked with an asterisk * only reexport modules under the
directory with the same name. Modules under the directory usually
consist of a `Base` module, which contains basic definitions, and
(possibly) several other modules with specific content, for example a
`Properties` module.

Modules marked with double asterisk ** instantiate the parameters of
a more general module and export the special instances.

Some modules are shared among the mechanizations of
&lambda;<sub>IK</sub> and &lambda;<sub>IS4</sub>. They contain code
that is (or is parameterized to be) calculi-independent.

- `Type.agda`: Syntax of types (common to &lambda;<sub>IK</sub> and &lambda;<sub>IS4</sub>)
- `Context.agda`: Syntax of contexts, weakenings/OPEs, substitutions, and properties (common to &lambda;<sub>IK</sub> and &lambda;<sub>IS4</sub>)
- `IK/`
  + `Term.agda`*
  + `Term/`
    * `Base.agda`: Syntax of terms, actions of weakening and substitution
    * `Properties.agda`: Properties of the actions of weakening and substitution on terms
    * `Reduction.agda`: Reduction relation on terms
    * `Conversion.agda`: Conversion relation on terms
    * `NormalForm.agda`*
    * `NormalForm/`
      + `Base.agda`: Syntax of normal and neutral forms, and action of weakening
      + `Properties.agda`: Properties of the action of weakening on normal and neutral forms
  + `Norm.agda`*
  + `Norm/`
    * `Base.agda`: Quote and normalization functions
    * `NbE/`
      + `Model.agda`: NbE model and evaluation function
      + `Reification.agda`: Reify and reflect functions
    * `Properties/`
      + `Completeness.agda`: Soundness of evaluation, completeness of normalization
      + `Soundness.agda`: Completeness of evaluation, soundness of normalization
      + `Soundness/`
        - `Trace.agda`: Logical relation and its fundamental theorem for soundness of normalization
- `IS4/`
  + `Term.agda`*
  + `Term/`
    * `Base.agda`: Syntax of terms, actions of weakening and substitution
    * `NormalForm.agda`*
    * `NormalForm/`
      + `Base.agda`: Syntax of normal and neutral forms, and action of weakening
      + `Properties.agda`: Properties of the action of weakening on normal and neutral forms
    * `Reduction.agda`: Reduction relation on terms
    * `Conversion.agda`: Conversion relation on terms
    * `Properties.agda`: Properties of the actions of weakening and substitution on terms
  + `Norm.agda`*
  + `Norm/`
    * `Base.agda`: Quote and normalization functions
    * `NbE/`
      + `Model.agda`: NbE model and evaluation function (by instantiation of possible-worlds/presheaf semantics)
      + `Reification.agda`: Reify and reflect functions
    * `Properties/`
      + `Completeness.agda`: Completeness of normalization (by soundness of possible-worlds semantics)
      + `Soundness.agda`: Logical relation and its fundamental theorem for soundness of normalization
  + `Applications/`
    * `Purity.agda`: Normalization function for &lambda;<sub>IS4</sub>+Moggi and some properties
    * `IS4Plus.agda`: Normalization function for &lambda;<sub>IK</sub>+Bool and some properties
- `Semantics/`
  + `Clouston/`
    * `Evaluation/`
      + `IML.agda`**
      + `IML/`
        - `Base.agda`: Clouston's evaluation function for types, contexts, variables and weakenings (common to &lambda;<sub>IK</sub> and &lambda;<sub>IS4</sub>)
	- `Properties.agda`: Soundness of Clouston's categorical semantics of variables and weakenings
      + `IS4.agda`**
      + `IS4/`
        - `Base.agda`: Clouston's evaluation function for &lambda;<sub>IS4</sub>
        - `Properties.agda`: Soundness of Clouston's categorical semantics of &lambda;<sub>IS4</sub>
  + `Presheaf/`
    * `Base.agda`: Basic categorical structure of possible-worlds semantics (the interpretation of types, contexts, terms, substitutions, and action of substitution)
    * `CartesianClosure.agda`: Cartesian closure structure of possible-worlds semantics (the interpretation of context extension, product types, and function types)
    * `Necessity.agda`: Adjunction structure of possible-worlds semantics (the interpretation of lock context operator and box types)
    * `Evaluation/`
      + `IML.agda`: Evaluation function for &lambda;<sub>IK</sub> and its soundness (by instantiation of Clouston's categorical semantics with the categorical structure of possible-worlds semantics)
      + `IS4.agda`: Evaluation function for &lambda;<sub>IS4</sub> and its soundness (by instantiation of Clouston's categorical semantics with the categorical structure of possible-worlds semantics)
- `FunExt.agda`: Function extensionality axiom
- `HEUtil.agda`: Utilities for working with heterogeneous equality
- `EUtil.agda`: Utilities for working with negation
- `PUtil.agda`: Utilities for working with sigma types
- `PEUtil.agda`: Utilities for working with propositional equality
- `RUtil.agda`: Utilities for working with binary relations
- `Everything.agda`: Imports main modules for easy typechecking of the artifact
