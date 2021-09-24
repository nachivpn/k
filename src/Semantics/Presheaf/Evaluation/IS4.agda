open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Presheaf.Evaluation.IS4
  (C                  : Set)

  (_⩽_                : (X Y : C) → Set)

  (⩽-trans            : ∀ {X X' X'' : C} (f : X ⩽ X') (g : X' ⩽ X'') → X ⩽ X'')
  (⩽-trans-assoc      : ∀ {X X' X'' X''' : C} (f : X ⩽ X') (g : X' ⩽ X'') (h : X'' ⩽ X''') → ⩽-trans f (⩽-trans g h) ≡ ⩽-trans (⩽-trans f g) h)

  (⩽-refl             : ∀ {X : C} → X ⩽ X)

  (_R_                : (X Y : C) → Set)

  (R-trans            : ∀ {X Y Z : C} (r : X R Y) (r' : Y R Z) → X R Z)
  (R-trans-assoc      : ∀ {X Y Z Z' : C} (r : X R Y) (r' : Y R Z) (r'' : Z R Z') → R-trans r (R-trans r' r'') ≡ R-trans (R-trans r r') r'')

  (R-refl             : ∀ {X : C} → X R X)
  (R-refl-unit-left   : ∀ {X Y : C} (r : X R Y) → R-trans r R-refl ≡ r)
  (R-refl-unit-right  : ∀ {X Y : C} (r : X R Y) → R-trans R-refl r ≡ r)

  (factor1            : ∀ {X X' Y' : C} (w : X ⩽ X') (r : X' R Y') → ∃ λ Y → X R Y ∧ Y ⩽ Y')
  (let factor1C       : {X X' Y' : C} → (w : X ⩽ X') → (r : X' R Y') → C    ; factor1C = λ w r → factor1 w r .fst)
  (let factor1R       : ∀ {X X' Y' : C} (w : X ⩽ X') (r : X' R Y') → X R _  ; factor1R = λ w r → factor1 w r .snd .fst)
  (let factor1⩽       : ∀ {X X' Y' : C} (w : X ⩽ X') (r : X' R Y') → _ ⩽ Y' ; factor1⩽ = λ w r → factor1 w r .snd .snd)

  (factor2            : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → ∃ λ X' → X ⩽ X' ∧ X' R Y')
  (let factor2C       : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → C      ; factor2C r w = factor2 r w .fst)
  (let factor2⩽       : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → X ⩽ _  ; factor2⩽ r w = factor2 r w .snd .fst)
  (let factor2R       : ∀ {X Y Y' : C} (r : X R Y) (w : Y ⩽ Y') → _ R Y' ; factor2R r w = factor2 r w .snd .snd)
  (factor2-pres-refl  : ∀ {X X' : C} (w : X ⩽ X') → factor2 R-refl w ≡ (X' , w , R-refl))
  (factor2-pres-trans : ∀ {X Y Z Z' : C} (r : X R Y) (r' : Y R Z) (w : Z ⩽ Z') → factor2 (R-trans r r') w ≡ (factor2C r (factor2⩽ r' w) , factor2⩽ r _ , R-trans (factor2R r _) (factor2R r' _)))
  -- (factor2-pres-id    : ∀ {X Y : C} (r : X R Y) → factor2 r ⩽-refl ≡ (-, ⩽-refl , r))
  -- (factor2-pres-∘     : ∀ {X Y Y' Y'' : C} (r : X R Y) (w : Y ⩽ Y') (w' : Y' ⩽ Y'') → factor2 r (⩽-trans w w') ≡ (-, ⩽-trans (factor2⩽ r w) (factor2⩽ (factor2R r w) w') , factor2R (factor2R r w) w'))

  (factor2-factor1    : ∀ {X X' Y' : C} → (w : X ⩽ X') → (r : X' R Y') → factor2 (factor1R w r) (factor1⩽ w r) ≡ (-, w , r))
  (factor1-factor2    : ∀ {X Y  Y' : C} → (r : X R Y)  → (w : Y ⩽ Y')  → factor1 (factor2⩽ r w) (factor2R r w) ≡ (-, r , w))
  where

import Semantics.Presheaf.Base C _⩽_ as PresheafBase
import Semantics.Presheaf.CartesianClosure C _⩽_ ⩽-refl ⩽-trans ⩽-trans-assoc as PresheafCartesianClosure
import Semantics.Presheaf.Necessity C _⩽_ ⩽-refl ⩽-trans _R_ factor1 factor2 factor2-factor1 factor1-factor2 as PresheafNecessity

module PresheafNecessityIS4 = PresheafNecessity.IS4 R-trans R-trans-assoc R-refl R-refl-unit-left R-refl-unit-right factor2-pres-refl factor2-pres-trans

open PresheafBase             public
open PresheafCartesianClosure public
open PresheafNecessity        public
open PresheafNecessityIS4     public

import Semantics.Clouston.Evaluation.IS4.Base
    Psh _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ ∘-pres-≈̇ ∘-assoc id'[_] id'-unit-left id'-unit-right
    []' unit' []'-eta _×'_ ⟨_,_⟩' ⟨,⟩'-pres-≈̇ π₁'[_] π₂'[_] ×'-beta-left ×'-beta-right ×'-eta ⟨,⟩'-nat
    _⇒'_ lam' app'
    ✦'_ ✦'-map_ ✦'-map-pres-≈̇ ✦'-map-pres-id' η'[_] μ'[_]
    □'_ box' λ'
  as CloustonEvaluationIS4Base

open CloustonEvaluationIS4Base public

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
