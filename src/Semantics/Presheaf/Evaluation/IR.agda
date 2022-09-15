{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Presheaf.Evaluation.IR
  (C                 : Set)

  (_⩽_               : (X Y : C) → Set)

  (⩽-trans           : ∀ {X X' X'' : C} (f : X ⩽ X') (g : X' ⩽ X'') → X ⩽ X'')
  (⩽-trans-assoc     : ∀ {X X' X'' X''' : C} (f : X ⩽ X') (g : X' ⩽ X'') (h : X'' ⩽ X''') → ⩽-trans f (⩽-trans g h) ≡ ⩽-trans (⩽-trans f g) h)

  (⩽-refl            : ∀ {X : C} → X ⩽ X)
  (⩽-refl-unit-left  : ∀ {X X' : C} (f : X ⩽ X') → ⩽-trans f ⩽-refl ≡ f)
  (⩽-refl-unit-right : ∀ {X X' : C} (f : X ⩽ X') → ⩽-trans ⩽-refl f ≡ f)

  (_R_               : (X Y : C) → Set)

  (R-sub             : ∀ {X Y : C} (r : X R Y) → X ⩽ Y)

  (factor            : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → ∃ λ X' → X ⩽ X' ∧ X' R Y')
  (let lCtx          : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → C      ; lCtx     = λ r w → factor r w .fst)
  (let factorWk      : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → X ⩽ _  ; factorWk = λ r w → factor r w .snd .fst)
  (let factorR       : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → _ R Y' ; factorR  = λ r w → factor r w .snd .snd)
  (factor-pres-id    : ∀ {X Y : C} (r : X R Y) → factor r ⩽-refl ≡ (-, ⩽-refl , r))
  (factor-pres-∘     : ∀ {X Y Y' Y'' : C} (r : X R Y) (w : Y ⩽ Y') (w' : Y' ⩽ Y'') → factor r (⩽-trans w w') ≡ (-, ⩽-trans (factorWk r w) (factorWk (factorR r w) w') , factorR (factorR r w) w'))
  (factor-comm       : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → ⩽-trans (factorWk r w) (R-sub (factorR r w)) ≡ ⩽-trans (R-sub r) w)
  where

import Semantics.Presheaf.Base C _⩽_ ⩽-refl ⩽-trans as PresheafBase
import Semantics.Presheaf.CartesianClosure C _⩽_ ⩽-trans ⩽-trans-assoc ⩽-refl ⩽-refl-unit-left ⩽-refl-unit-right as PresheafCartesianClosure
import Semantics.Presheaf.Necessity C _⩽_ ⩽-trans ⩽-trans-assoc ⩽-refl ⩽-refl-unit-left ⩽-refl-unit-right _R_ factor factor-pres-id factor-pres-∘ as PresheafNecessity

module PresheafNecessityIR = PresheafNecessity.IR R-sub factor-comm

open PresheafBase             public
open PresheafCartesianClosure public
open PresheafNecessity        public
open PresheafNecessityIR      public

import Semantics.Clouston.Evaluation.IR.Base
    Psh _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ id'[_]
    []' unit' _×'_ ⟨_,_⟩' π₁'[_] π₂'[_]
    _⇒'_ lam' app'
    ✦'_ ✦'-map_ ε'[_]
    □'_ box' λ'
  as CloustonEvaluationIRBase

open CloustonEvaluationIRBase public using (module Eval)
