# k

Normalisation for Fitch-style Modal Calculi

## About

Fitch-style modal lambda calculi enable programming with necessity
modalities in a typed lambda calculus by extending the typing context
with a delimiting operator that is denoted by a lock. The addition of
locks simplifies the formulation of typing rules for calculi that
incorporate different modal axioms, but each variant demands different,
tedious and seemingly ad hoc syntactic lemmas to prove normalization.

This repo contains a mechanisation of some intrinsically-typed
Fitch-style modal lambda calculi and a proof of normalization for them.
Normalization is achieved using normalization by evaluation
(NbE), by leveraging the possible-world semantics of
Fitch-style calculi. The semantics-based approach
of NbE yields a more modular approach to normalization
that allows us to separate reasoning about the modal fragment
from the rest of the calculus.

## Current status

Implements executable normalisation functions for IK (the calculus
with the modal axiom K) and IS4 (the calculus with axioms K, T and 4),
and a "tracing" function for each calculus that prints out a
sequence of reduction steps that explain the result of the
normalisation function. This yields a proof of completeness
for normalisation, i.e., norm t = norm t' => t ~ t'.

## References

* Ranald Clouston. 2018. [Fitch-Style Modal Lambda Calculi](https://arxiv.org/abs/1710.08326).
* V.A.J. Borghuis. 1994. [Coming to terms with modal logic: on the interpretation of modalities in typed lambda-calculus](https://research.tue.nl/en/publications/coming-to-terms-with-modal-logic-on-the-interpretation-of-modalit).
