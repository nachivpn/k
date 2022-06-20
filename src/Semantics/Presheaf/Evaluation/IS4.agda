{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Presheaf.Evaluation.IS4
  (C                 : Set)

  (_⩽_               : (X Y : C) → Set)

  (⩽-trans           : ∀ {X X' X'' : C} (f : X ⩽ X') (g : X' ⩽ X'') → X ⩽ X'')
  (⩽-trans-assoc     : ∀ {X X' X'' X''' : C} (f : X ⩽ X') (g : X' ⩽ X'') (h : X'' ⩽ X''') → ⩽-trans f (⩽-trans g h) ≡ ⩽-trans (⩽-trans f g) h)

  (⩽-refl            : ∀ {X : C} → X ⩽ X)
  (⩽-refl-unit-left  : ∀ {X X' : C} (f : X ⩽ X') → ⩽-trans f ⩽-refl ≡ f)
  (⩽-refl-unit-right : ∀ {X X' : C} (f : X ⩽ X') → ⩽-trans ⩽-refl f ≡ f)

  (_R_               : (X Y : C) → Set)

  (R-trans           : ∀ {X Y Z : C} (r : X R Y) (r' : Y R Z) → X R Z)
  (R-trans-assoc     : ∀ {X Y Z Z' : C} (r : X R Y) (r' : Y R Z) (r'' : Z R Z') → R-trans r (R-trans r' r'') ≡ R-trans (R-trans r r') r'')

  (R-refl            : ∀ {X : C} → X R X)
  (R-refl-unit-left  : ∀ {X Y : C} (r : X R Y) → R-trans r R-refl ≡ r)
  (R-refl-unit-right : ∀ {X Y : C} (r : X R Y) → R-trans R-refl r ≡ r)

  (factor            : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → ∃ λ X' → X ⩽ X' ∧ X' R Y')
  (let lCtx          : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → C      ; lCtx     = λ r w → factor r w .fst)
  (let factorWk      : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → X ⩽ _  ; factorWk = λ r w → factor r w .snd .fst)
  (let factorR       : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → _ R Y' ; factorR  = λ r w → factor r w .snd .snd)
  (factor-pres-id    : ∀ {X Y : C} (r : X R Y) → factor r ⩽-refl ≡ (-, ⩽-refl , r))
  (factor-pres-∘     : ∀ {X Y Y' Y'' : C} (r : X R Y) (w : Y ⩽ Y') (w' : Y' ⩽ Y'') → factor r (⩽-trans w w') ≡ (-, ⩽-trans (factorWk r w) (factorWk (factorR r w) w') , factorR (factorR r w) w'))
  (factor-pres-refl  : ∀ {X X' : C} (w : X ⩽ X') → factor R-refl w ≡ (X' , w , R-refl))
  (factor-pres-trans : ∀ {X Y Z Z' : C} (r : X R Y) (r' : Y R Z) (w : Z ⩽ Z') → factor (R-trans r r') w ≡ (lCtx r (factorWk r' w) , factorWk r _ , R-trans (factorR r _) (factorR r' _)))
  where

import Semantics.Presheaf.Base C _⩽_ ⩽-refl ⩽-trans as PresheafBase
import Semantics.Presheaf.CartesianClosure C _⩽_ ⩽-trans ⩽-trans-assoc ⩽-refl ⩽-refl-unit-left ⩽-refl-unit-right as PresheafCartesianClosure
import Semantics.Presheaf.Necessity C _⩽_ ⩽-trans ⩽-trans-assoc ⩽-refl ⩽-refl-unit-left ⩽-refl-unit-right _R_ factor factor-pres-id factor-pres-∘ as PresheafNecessity

module PresheafNecessityIS4 = PresheafNecessity.IS4 R-trans R-trans-assoc R-refl R-refl-unit-left R-refl-unit-right factor-pres-refl factor-pres-trans

open PresheafBase             public
open PresheafCartesianClosure public
open PresheafNecessity        public
open PresheafNecessityIS4     public

import Semantics.Clouston.Evaluation.IS4.Base
    Psh _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ id'[_]
    []' unit' _×'_ ⟨_,_⟩' π₁'[_] π₂'[_]
    _⇒'_ lam' app'
    ✦'_ ✦'-map_ μ'[_] η'[_]
    □'_ box' λ'
  as CloustonEvaluationIS4Base

open CloustonEvaluationIS4Base public using (module Eval)

module EvalProperties (N : Psh) where
  import Semantics.Clouston.Evaluation.IS4.Properties
      Psh _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ ∘-pres-≈̇ ∘-assoc id'[_] id'-unit-left id'-unit-right
      []' unit' []'-eta _×'_ ⟨_,_⟩' ⟨,⟩'-pres-≈̇ π₁'[_] π₂'[_] ×'-beta-left ×'-beta-right ×'-eta ⟨,⟩'-nat
      _⇒'_ lam' lam'-pres-≈̇ app' app'-pres-≈̇ ⇒'-beta ⇒'-eta lam'-nat app'-nat
      ✦'_ ✦'-map_ ✦'-map-pres-≈̇ ✦'-map-pres-id' ✦'-map-pres-∘ μ'[_] μ'-nat μ'-assoc[_] η'[_] η'-nat η'-unit-left[_] η'-unit-right[_]
      □'_ □'-map_ box' box'-pres-≈̇ λ' λ'-pres-≈̇ □'-beta □'-eta box'-nat-dom λ'-nat-dom
      N
    as CloustonEvaluationIS4Properties

  open CloustonEvaluationIS4Properties public
