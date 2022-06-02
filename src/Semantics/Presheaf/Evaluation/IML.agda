{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Presheaf.Evaluation.IML
  (C                 : Set)
  (_⩽_               : (X Y : C) → Set)
  (⩽-trans           : ∀ {X X' X'' : C} (f : X ⩽ X') (g : X' ⩽ X'') → X ⩽ X'')
  (⩽-trans-assoc     : ∀ {X X' X'' X''' : C} (f : X ⩽ X') (g : X' ⩽ X'') (h : X'' ⩽ X''') → ⩽-trans f (⩽-trans g h) ≡ ⩽-trans (⩽-trans f g) h)
  (⩽-refl            : ∀ {X : C} → X ⩽ X)
  (⩽-refl-unit-left  : ∀ {X X' : C} (f : X ⩽ X') → ⩽-trans ⩽-refl f ≡ f)
  (⩽-refl-unit-right : ∀ {X X' : C} (f : X ⩽ X') → ⩽-trans f ⩽-refl ≡ f)
  (_R_               : (X Y : C) → Set)
  (factor            : ∀ {X Y Y' : C} → (r : X R Y) → (w : Y ⩽ Y') → ∃ λ X' → X ⩽ X' ∧ X' R Y')
  (let lCtx          : {Γ Δ Δ' : C} → (r : Γ R Δ) → (w : Δ ⩽ Δ') → C    ; lCtx     = λ r w → factor r w .fst)
  (let factorWk      : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⩽ Δ') → Γ ⩽ _  ; factorWk = λ r w → factor r w .snd .fst)
  (let factorR       : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⩽ Δ') → _ R Δ' ; factorR  = λ r w → factor r w .snd .snd)
  (factor-pres-id    : ∀ {X Y : C} (r : X R Y) → factor r ⩽-refl ≡ (-, ⩽-refl , r))
  (factor-pres-∘     : ∀ {X Y Y' Y'' : C} (r : X R Y) (w : Y ⩽ Y') (w' : Y' ⩽ Y'') → factor r (⩽-trans w w') ≡ (-, ⩽-trans (factorWk r w) (factorWk (factorR r w) w') , factorR (factorR r w) w'))
  where

open import Level using (0ℓ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Type

open import Context (Ty)

import Semantics.Presheaf.Base
  C _⩽_ ⩽-refl ⩽-trans
  as PresheafBase
import Semantics.Presheaf.CartesianClosure
  C _⩽_ ⩽-trans ⩽-trans-assoc ⩽-refl ⩽-refl-unit-right ⩽-refl-unit-left
  as PresheafCartesianClosure
import Semantics.Presheaf.Necessity
  C _⩽_ ⩽-trans ⩽-trans-assoc ⩽-refl ⩽-refl-unit-right ⩽-refl-unit-left _R_ factor factor-pres-id factor-pres-∘
  as PresheafNecessity

open PresheafBase             public
open PresheafCartesianClosure public
open PresheafNecessity        public

import Semantics.Clouston.Evaluation.IML
  Psh _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ ∘-pres-≈̇ ∘-assoc id'[_] id'-unit-left id'-unit-right
  []' unit' []'-eta _×'_ ⟨_,_⟩' ⟨,⟩'-pres-≈̇ π₁'[_] π₂'[_] ×'-beta-left ×'-beta-right ×'-eta ⟨,⟩'-nat
  _⇒'_
  ✦'_ ✦'-map_ ✦'-map-pres-≈̇ ✦'-map-pres-id'
  □'_
  as CloustonEvaluationIML

module Eval (N : Psh) where
  module CloustonEvaluationIMLEval = CloustonEvaluationIML.Eval N

  open CloustonEvaluationIMLEval public
