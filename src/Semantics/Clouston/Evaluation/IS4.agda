{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Clouston.Evaluation.IS4
  (Ctx' : Set₁)

  (_→̇_ : (P Q : Ctx') → Set) (let infixr 19 _→̇_; _→̇_ = _→̇_)

  (_≈̇_     : {P Q : Ctx'} → (φ ψ : P →̇ Q) → Set) (let infix 18 _≈̇_; _≈̇_ = _≈̇_)
  (≈̇-refl  : ∀ {P Q : Ctx'} {φ : P →̇ Q} → φ ≈̇ φ)
  (≈̇-sym   : ∀ {P Q : Ctx'} {φ ψ : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → ψ ≈̇ φ)
  (≈̇-trans : ∀ {P Q : Ctx'} {φ ψ ω : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → (ψ≈̇ω : ψ ≈̇ ω) → φ ≈̇ ω)

  (_∘_      : {P Q R : Ctx'} → (ψ : Q →̇ R) → (φ : P →̇ Q) → (P →̇ R)) (let infixr 19 _∘_; _∘_ = _∘_)
  (∘-pres-≈̇ : ∀ {P Q R : Ctx'} {ψ ψ' : Q →̇ R} {φ φ' : P →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ' ∘ φ')
  (∘-assoc  : {P Q R S : Ctx'} → (ω : R →̇ S) → (ψ : Q →̇ R) → (φ : P →̇ Q) → (ω ∘ ψ) ∘ φ ≈̇ ω ∘ ψ ∘ φ)
  (let _[_]' = _∘_)

  (id'[_]         : (P : Ctx') → P →̇ P)
  (id'-unit-left  : ∀ {P : Ctx'} (Q : Ctx') (φ : P →̇ Q) → id'[ Q ] ∘ φ ≈̇ φ)
  (id'-unit-right : ∀ (P : Ctx') {Q : Ctx'} (φ : P →̇ Q) → φ ∘ id'[ P ] ≈̇ φ)

  ([]'     : Ctx')
  (unit'   : {P : Ctx'} → P →̇ []')
  ([]'-eta : ∀ {P : Ctx'} {φ : P →̇ []'} → φ ≈̇ unit')

  (_×'_          : (P Q : Ctx') → Ctx')
  (⟨_,_⟩'        : {R P Q : Ctx'} → (φ : R →̇ P) → (ψ : R →̇ Q) → R →̇ P ×' Q)
  (⟨,⟩'-pres-≈̇   : ∀ {R P Q : Ctx'} {φ φ' : R →̇ P} {ψ ψ' : R →̇ Q} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ' ⟩')
  (π₁'[_]        : {P : Ctx'} → (Q : Ctx') → P ×' Q →̇ P)
  (π₂'[_]        : (P : Ctx') → {Q : Ctx'} → P ×' Q →̇ Q)
  (let fst'[_]_ = λ {R} {P} Q φ → _∘_ {R} {P ×' Q} {P} π₁'[ Q ] φ)
  (let snd'[_]_ = λ {R} P {Q} φ → _∘_ {R} {P ×' Q} {Q} π₂'[ P ] φ)
  (×'-beta-left  : ∀ {R P Q : Ctx'} {φ : R →̇ P} (ψ : R →̇ Q) → π₁'[ Q ] ∘ ⟨ φ , ψ ⟩' ≈̇ φ)
  (×'-beta-right : ∀ {R P Q : Ctx'} (φ : R →̇ P) {ψ : R →̇ Q} → π₂'[ P ] ∘ ⟨ φ , ψ ⟩' ≈̇ ψ)
  (×'-eta        : ∀ {R P Q : Ctx'} {φ : R →̇ P ×' Q} → φ ≈̇ ⟨ fst'[ Q ] φ , snd'[ P ] φ ⟩')
  (⟨,⟩'-nat      : ∀ {R' R P Q : Ctx'} (φ : R →̇ P) (ψ : R →̇ Q) (ω : R' →̇ R) → ⟨ φ , ψ ⟩' ∘ ω ≈̇ ⟨ φ ∘ ω , ψ ∘ ω ⟩')
  (let _×'-map_ = λ {P} {P'} {Q} {Q'} φ ψ → ⟨_,_⟩' {P ×' Q} {P'} {Q'} (φ ∘ π₁'[ Q ]) (ψ ∘ π₂'[ P ]))

  (let Ty' = Ctx')

  (_⇒'_        : (P Q : Ty') → Ty')
  (lam'        : {R P Q : Ty'} → (φ : R ×' P →̇ Q) → R →̇ P ⇒' Q)
  (lam'-pres-≈̇ : ∀ {R P Q : Ty'} {φ φ' : R ×' P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → lam' φ ≈̇ lam' φ')
  (app'        : {R P Q : Ty'} → (φ : R →̇ P ⇒' Q) → (ψ : R →̇ P) → R →̇ Q)
  (app'-pres-≈̇ : ∀ {R P Q : Ty'} {φ φ' : R →̇ P ⇒' Q} {ψ ψ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → app' φ ψ ≈̇ app' φ' ψ')
  (⇒'-beta     : ∀ {R P Q : Ty'} (φ : R ×' P →̇ Q) (ψ : R →̇ P) → app' (lam' φ) ψ ≈̇ φ [ ⟨ id'[ R ] , ψ ⟩' ]')
  (⇒'-eta      : ∀ {R P Q : Ty'} (φ : R →̇ P ⇒' Q) → φ ≈̇ lam' (app' (φ [ π₁'[ P ] ]') π₂'[ R ]))
  (lam'-nat    : ∀ {R' R P Q : Ty'} (φ : R ×' P →̇ Q) (ψ : R' →̇ R) → lam' φ ∘ ψ ≈̇ lam' (φ ∘ ψ ×'-map id'[ P ]))
  (app'-nat    : ∀ {R' R P Q : Ty'} (φ : R →̇ P ⇒' Q) (ψ : R →̇ P) (ω : R' →̇ R) → app' φ ψ ∘ ω ≈̇ app' (φ ∘ ω) (ψ ∘ ω))

  (✦'_              : (P : Ctx') → Ctx')
  (✦'-map_          : {P Q : Ctx'} → (φ : P →̇ Q) → ✦' P →̇ ✦' Q)
  (✦'-map-pres-≈̇    : {P Q : Ctx'} {φ φ' : P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → ✦'-map φ ≈̇ ✦'-map φ')
  (✦'-map-pres-id'  : {P : Ctx'} → ✦'-map id'[ P ] ≈̇ id'[ ✦' P ])
  (✦'-map-pres-∘    : {P Q R : Ctx'} (ψ : Q →̇ R) (φ : P →̇ Q) → ✦'-map (ψ ∘ φ) ≈̇ ✦'-map ψ ∘ ✦'-map φ)
  (μ'[_]            : (P : Ctx') → ✦' ✦' P →̇ ✦' P)
  (μ'-nat           : ∀ {P Q : Ctx'} (φ : P →̇ Q) → ✦'-map φ ∘ μ'[ P ] ≈̇ μ'[ Q ] ∘ ✦'-map ✦'-map φ)
  (μ'-assoc[_]      : ∀ (P : Ctx') → μ'[ P ] ∘ μ'[ ✦' P ] ≈̇ μ'[ P ] ∘ ✦'-map μ'[ P ])
  (η'[_]            : (P : Ctx') → P →̇ ✦' P)
  (η'-nat           : ∀ {P Q : Ctx'} (φ : P →̇ Q) → ✦'-map φ ∘ η'[ P ] ≈̇ η'[ Q ] ∘ φ)
  (η'-unit-left[_]  : ∀ (P : Ctx') → μ'[ P ] ∘ η'[ ✦' P ] ≈̇ id'[ ✦' P ])
  (η'-unit-right[_] : ∀ (P : Ctx') → μ'[ P ] ∘ ✦'-map η'[ P ] ≈̇ id'[ ✦' P ])

  (□'_          : (P : Ty') → Ty')
  (□'-map_      : {P Q : Ctx'} → (φ : P →̇ Q) → □' P →̇ □' Q)
  (box'         : {P Q : Ty'} → (φ : ✦' P →̇ Q) → P →̇ □' Q)
  (box'-pres-≈̇  : ∀ {P : Ctx'} {Q : Ty'} {φ φ' : ✦' P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → box' φ ≈̇ box' φ')
  (λ'           : {P Q : Ty'} → (φ : P →̇ □' Q) → ✦' P →̇ Q)
  (λ'-pres-≈̇    : ∀ {P : Ctx'} {Q : Ty'} {φ φ' : P →̇ □' Q} (φ≈̇φ' : φ ≈̇ φ') → λ' φ ≈̇ λ' φ')
  (□'-beta      : ∀ {P : Ctx'} {Q : Ty'} (φ : ✦' P →̇ Q) → λ' (box' φ) ≈̇ φ)
  (□'-eta       : ∀ {P : Ctx'} {Q : Ty'} (φ : P →̇ □' Q) → φ ≈̇ box' (λ' φ))
  (box'-nat-dom : ∀ {P' P : Ctx'} {Q : Ty'} (φ : ✦' P →̇ Q) (φ' : P' →̇ P) → box' (φ ∘ ✦'-map φ') ≈̇ box' φ ∘ φ')
  (λ'-nat-dom   : ∀ {P' P : Ctx'} {Q : Ty'} (φ : P →̇ □' Q) (φ' : P' →̇ P) → λ' (φ ∘ φ') ≈̇ λ' φ ∘ ✦'-map φ')
  where

import Semantics.Clouston.Evaluation.IS4.Base
    Ctx' _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ id'[_]
    []' unit' _×'_ ⟨_,_⟩' π₁'[_] π₂'[_]
    _⇒'_ lam' app'
    ✦'_ ✦'-map_ μ'[_] η'[_]
    □'_ box' λ'
  as CloustonEvaluationIS4Base

open CloustonEvaluationIS4Base public

module EvalProperties (N : Ty') where
  import Semantics.Clouston.Evaluation.IS4.Properties
      Ctx' _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ ∘-pres-≈̇ ∘-assoc id'[_] id'-unit-left id'-unit-right
      []' unit' []'-eta _×'_ ⟨_,_⟩' ⟨,⟩'-pres-≈̇ π₁'[_] π₂'[_] ×'-beta-left ×'-beta-right ×'-eta ⟨,⟩'-nat
      _⇒'_ lam' lam'-pres-≈̇ app' app'-pres-≈̇ ⇒'-beta ⇒'-eta lam'-nat app'-nat
      ✦'_ ✦'-map_ ✦'-map-pres-≈̇ ✦'-map-pres-id' ✦'-map-pres-∘ μ'[_] μ'-nat μ'-assoc[_] η'[_] η'-nat η'-unit-left[_] η'-unit-right[_]
      □'_ □'-map_ box' box'-pres-≈̇ λ' λ'-pres-≈̇ □'-beta □'-eta box'-nat-dom λ'-nat-dom N
    as CloustonEvaluationIS4Properties

  open CloustonEvaluationIS4Properties public
