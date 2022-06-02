{-# OPTIONS --safe --with-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_)

module Everything
  (funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
           → ((x : A) → f x ≡ g x) → f ≡ g)
  (funexti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
           → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g) where

import Type
import Context
import HEUtil

import IK.Term
import IK.Term.Conversion
import IK.Term.NormalForm
import IK.Term.Reduction
import IK.Term.Substitution

import IK.Norm
import IK.Norm.NbE.Model
import IK.Norm.NbE.Reification
open import IK.Norm.Properties.Completeness.Completeness funext funexti
import IK.Norm.Properties.Soundness.Soundness
import IK.Norm.Properties.Soundness.Trace

import IK.Applications.Experiments
import IK.Applications.Neutrality
import IK.Applications.WeakNorm

import IS4.Term
import IS4.Term.Conversion
import IS4.Term.NormalForm
import IS4.Term.Reduction

import IS4.Norm
import IS4.Norm.NbE.Model
import IS4.Norm.NbE.Reification
import IS4.Norm.Properties.Completeness
import IS4.Norm.Properties.Soundness

import IS4.Applications.IS4Plus
import IS4.Applications.Purity

import Semantics.Clouston.Evaluation.IML
import Semantics.Clouston.Evaluation.IS4

import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.Evaluation.IML
import Semantics.Presheaf.Evaluation.IS4
import Semantics.Presheaf.Necessity
