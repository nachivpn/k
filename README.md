# k
Mechanization of Fitch-style Intuitionistic K in Agda

## About

Fitch-style modal lambda calculi provide an elegant approach to programming
necessitation (or "box") modalities by extending typed-lambda calculi with 
a delimiting context operator (or "lock"). 
The addition of locks simplifies the formulation of typing rules for 
different modalities, but obscures syntactic lemmas 
involving the context, and makes it difficult to formalize 
and prove meta-theoretic properties about these calculi.

This repo contains a mechanization of an intrinsically typed formalization 
of the Fitch-style Intuitionistic K (IK) calculus in Agda. The trick 
here is to identify a suitable inductive notion of weakening and 
parallel substitution that is amenable to implementation and proofs.
These are then used to guide the development of a normalization-by-evaluation 
procedure for IK.

## Current status

Implements an executable normalization function for IK, and a "tracing" function that prints 
out a sequence of reduction steps that explain the result of the normalization function.
The latter yields a proof of completness for normalization, i.e., norm t = norm t' => t ~ t'.

## Plan

I'd like to prove confluence and decidability for IK (which demand soundness of normalization), 
and illustrate applications of normalization in modal logic, and possibly in partial evaluation. 
If all this goes well, then I'll probably turn to S4 next. 


Thoughts?

## References

* Ranald Clouston. 2018. [Fitch-Style Modal Lambda Calculi](https://arxiv.org/abs/1710.08326).
* V.A.J. Borghuis. 1994. [Coming to terms with modal logic: on the interpretation of modalities in typed lambda-calculus](https://research.tue.nl/en/publications/coming-to-terms-with-modal-logic-on-the-interpretation-of-modalit).

