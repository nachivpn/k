open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Presheaf.Evaluation.IML
  (C               : Set)
  (_⩽_             : (X Y : C) → Set)
  (⩽-refl          : ∀ {X : C} → X ⩽ X)
  (⩽-trans         : ∀ {X X' X'' : C} (f : X ⩽ X') (g : X' ⩽ X'') → X ⩽ X'')
  (⩽-trans-assoc   : ∀ {X X' X'' X''' : C} (f : X ⩽ X') (g : X' ⩽ X'') (h : X'' ⩽ X''') → ⩽-trans f (⩽-trans g h) ≡ ⩽-trans (⩽-trans f g) h)
  (_R_             : (X Y : C) → Set)
  (factor1         : ∀ {X X' Y' : C} → (w : X ⩽ X') → (r : X' R Y') → ∃ λ Y → X R Y ∧ Y ⩽ Y')
  (let factor1C    : {X X' Y' : C} → (w : X ⩽ X') → (r : X' R Y') → C    ; factor1C = λ w r → factor1 w r .fst)
  (let factor1R    : ∀ {X X' Y' : C} (w : X ⩽ X') (r : X' R Y') → X R _  ; factor1R = λ w r → factor1 w r .snd .fst)
  (let factor1⩽    : ∀ {X X' Y' : C} (w : X ⩽ X') (r : X' R Y') → _ ⩽ Y' ; factor1⩽ = λ w r → factor1 w r .snd .snd)
  (factor2         : ∀ {X Y Y' : C} → (r : X R Y) → (w : Y ⩽ Y') → ∃ λ X' → X ⩽ X' ∧ X' R Y')
  (let factor2C    : {Γ Δ Δ' : C} → (r : Γ R Δ) → (w : Δ ⩽ Δ') → C    ; factor2C = λ r w → factor2 r w .fst)
  (let factor2⩽    : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⩽ Δ') → Γ ⩽ _  ; factor2⩽ = λ r w → factor2 r w .snd .fst)
  (let factor2R    : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⩽ Δ') → _ R Δ' ; factor2R = λ r w → factor2 r w .snd .snd)
  (factor2-factor1 : ∀ {X X' Y' : C} → (w : X ⩽ X') → (r : X' R Y') → factor2 (factor1R w r) (factor1⩽ w r) ≡ (-, w , r))
  (factor1-factor2 : ∀ {X Y  Y' : C} → (r : X R Y)  → (w : Y ⩽ Y')  → factor1 (factor2⩽ r w) (factor2R r w) ≡ (-, r , w))
  where

open import Level using (0ℓ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import IK.Type

open import Context (Ty)

import Semantics.Presheaf.Base
  C _⩽_
  as PresheafBase
import Semantics.Presheaf.CartesianClosure
  C _⩽_ ⩽-refl ⩽-trans ⩽-trans-assoc
  as PresheafCartesianClosure
import Semantics.Presheaf.Necessity
  C _⩽_ ⩽-refl ⩽-trans _R_ factor1 factor2 factor2-factor1 factor1-factor2
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
