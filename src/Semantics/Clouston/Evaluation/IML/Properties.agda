{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Clouston.Evaluation.IML.Properties
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

  (✦'_             : (P : Ctx') → Ctx')
  (✦'-map_         : {P Q : Ctx'} → (φ : P →̇ Q) → ✦' P →̇ ✦' Q)
  (✦'-map-pres-≈̇   : {P Q : Ctx'} {φ φ' : P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → ✦'-map φ ≈̇ ✦'-map φ')
  (✦'-map-pres-id' : {P : Ctx'} → ✦'-map id'[ P ] ≈̇ id'[ ✦' P ])
  (✦'-map-pres-∘   : {P Q R : Ctx'} (ψ : Q →̇ R) (φ : P →̇ Q) → ✦'-map (ψ ∘ φ) ≈̇ ✦'-map ψ ∘ ✦'-map φ)

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

  (N : Ty')
  where

open import Level using (0ℓ)

open import Relation.Binary using (IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Type
open import Context Ty Ty-Decidable

open import Semantics.Clouston.Evaluation.IML.Base
    Ctx' _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ id'[_]
    []' unit' _×'_ ⟨_,_⟩' π₁'[_] π₂'[_]
    _⇒'_ lam' app'
    ✦'_ ✦'-map_
    □'_ box' λ'
  renaming (module Eval to CloustonEvaluationIMLBaseEval)

open CloustonEvaluationIMLBaseEval N

∘-pres-≈̇-left : ∀ {P Q R : Ctx'} {ψ ψ' : Q →̇ R} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ : P →̇ Q) → ψ ∘ φ ≈̇ ψ' ∘ φ
∘-pres-≈̇-left ψ≈̇ψ' φ = ∘-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

∘-pres-≈̇-right : ∀ {P Q R : Ctx'} (ψ : Q →̇ R) {φ φ' : P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ ∘ φ'
∘-pres-≈̇-right ψ φ≈̇φ' = ∘-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

abstract
  ⟨,⟩'-pres-≈̇-left : ∀ {R P Q : Ctx'} {φ φ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ Q) → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ ⟩'
  ⟨,⟩'-pres-≈̇-left ψ≈̇ψ' φ = ⟨,⟩'-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

  ⟨,⟩'-pres-≈̇-right : ∀ {R P Q : Ctx'} (φ : R →̇ P) {ψ ψ' : R →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ , ψ' ⟩'
  ⟨,⟩'-pres-≈̇-right ψ φ≈̇φ' = ⟨,⟩'-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

abstract
  ×'-map-pres-≈̇ : {P Q P' Q' : Ctx'} {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ' ×'-map ψ'
  ×'-map-pres-≈̇ {φ = φ} {φ'} φ≈̇φ' {ψ} {ψ'} ψ≈̇ψ' = let open EqReasoning (→̇-setoid _ _) in begin
    φ ×'-map ψ                ≡⟨⟩
    ⟨ φ  ∘ π₁' , ψ  ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (∘-pres-≈̇-left φ≈̇φ' π₁') (∘-pres-≈̇-left ψ≈̇ψ' π₂') ⟩
    ⟨ φ' ∘ π₁' , ψ' ∘ π₂' ⟩'  ∎

  ×'-map-pres-≈̇-left : {P Q P' : Ctx'} {φ φ' : P →̇ P'} (φ≈̇φ' : φ ≈̇ φ') (ψ : Q →̇ Q) → φ ×'-map ψ ≈̇ φ' ×'-map ψ
  ×'-map-pres-≈̇-left = λ φ≈̇φ' ψ → ×'-map-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

  ×'-map-pres-≈̇-right : {P Q Q' : Ctx'} (φ : P →̇ P) {ψ ψ' : Q →̇ Q'} (ψ≈̇ψ' : ψ ≈̇ ψ') → φ ×'-map ψ ≈̇ φ ×'-map ψ'
  ×'-map-pres-≈̇-right = λ φ ψ≈̇ψ' → ×'-map-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

  ×'-map-pres-id' : {P Q : Ctx'} → id'[ P ] ×'-map id'[ Q ] ≈̇ id'[ P ×' Q ]
  ×'-map-pres-id' {P} {Q} = let open EqReasoning (→̇-setoid _ _) in begin
    id' ×'-map id'              ≡⟨⟩
    ⟨ id' ∘ π₁' , id' ∘ π₂' ⟩'  ≈⟨ ⟨,⟩'-pres-≈̇ (id'-unit-left P π₁') (id'-unit-left Q π₂') ⟩
    ⟨ π₁'       , π₂'       ⟩'  ≈˘⟨ ⟨,⟩'-pres-≈̇ (id'-unit-right (P ×' Q) π₁') (id'-unit-right (P ×' Q) π₂') ⟩
    ⟨ π₁' ∘ id' , π₂' ∘ id' ⟩'  ≈˘⟨ ×'-eta ⟩
    id'                         ∎

abstract
  app'-pres-≈̇-left : ∀ {R : Ctx'} {P Q : Ty'} {φ φ' : R →̇ P ⇒' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ P) → app' φ ψ ≈̇ app' φ' ψ
  app'-pres-≈̇-left φ≈̇φ' ψ = app'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

  app'-pres-≈̇-right : ∀ {R : Ctx'} {P Q : Ty'} (φ : R →̇ P ⇒' Q) {ψ ψ' : R →̇ P} (ψ≈̇ψ' : ψ ≈̇ ψ') → app' φ ψ ≈̇ app' φ ψ'
  app'-pres-≈̇-right φ ψ≈̇ψ' = app'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

abstract
  unbox'-pres-≈̇ : ∀ {R P : Ctx'} {Q : Ty'} {φ φ' : P →̇ □' Q} (φ≈̇φ' : φ ≈̇ φ') {ψ ψ' : R →̇ ✦' P} (ψ≈̇ψ' : ψ ≈̇ ψ') → unbox' φ ψ ≈̇ unbox' φ' ψ'
  unbox'-pres-≈̇ φ≈̇φ' ψ≈̇ψ' = ∘-pres-≈̇ (λ'-pres-≈̇ φ≈̇φ') ψ≈̇ψ'

  unbox'-pres-≈̇-left : ∀ {R P : Ctx'} {Q : Ty'} {φ φ' : P →̇ □' Q} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ ✦' P) → unbox' φ ψ ≈̇ unbox' φ' ψ
  unbox'-pres-≈̇-left φ≈̇φ' ψ = unbox'-pres-≈̇ φ≈̇φ' (≈̇-refl {φ = ψ})

  unbox'-pres-≈̇-right : ∀ {R P : Ctx'} {Q : Ty'} (φ : P →̇ □' Q) {ψ ψ' : R →̇ ✦' P} (ψ≈̇ψ' : ψ ≈̇ ψ') → unbox' φ ψ ≈̇ unbox' φ ψ'
  unbox'-pres-≈̇-right φ ψ≈̇ψ' = unbox'-pres-≈̇ (≈̇-refl {φ = φ}) ψ≈̇ψ'

  unbox'-nat-dom : ∀ {R P' P : Ctx'} {Q : Ty'} (φ : P →̇ □' Q) (φ' : P' →̇ P) (ψ : R →̇ ✦' P') → unbox' (φ ∘ φ') ψ ≈̇ unbox' φ (✦'-map φ' ∘ ψ)
  unbox'-nat-dom {R} {P'} {P} {Q} φ φ' ψ = let open EqReasoning (→̇-setoid R Q) in begin
    unbox' (φ ∘ φ') ψ       ≡⟨⟩
    λ' (φ ∘ φ')        ∘ ψ  ≈⟨ ∘-pres-≈̇-left (λ'-nat-dom φ φ') ψ ⟩
    (λ' φ ∘ ✦'-map φ') ∘ ψ  ≈⟨ ∘-assoc (λ' φ) (✦'-map φ') ψ ⟩
    λ' φ ∘ ✦'-map φ' ∘ ψ    ∎

abstract
  evalWk-pres-id : ∀ (Γ : Ctx) → evalWk idWk[ Γ ] ≈̇ id'
  evalWk-pres-id []          = ≈̇-sym []'-eta
  evalWk-pres-id Γ@(Γ' `, a) = let open EqReasoning (Sub'-setoid Γ Γ) in begin
    evalWk (keep[ a ] idWk[ Γ' ])             ≈⟨ ×'-map-pres-≈̇-left (evalWk-pres-id Γ') id'[ evalTy a ] ⟩
    id'[ evalCtx Γ' ] ×'-map id'[ evalTy a ]  ≈⟨ ×'-map-pres-id' ⟩
    id'[ evalCtx Γ ]                          ∎
  evalWk-pres-id Γ@(Γ' #) = let open EqReasoning (Sub'-setoid Γ Γ) in begin
    evalWk (keep# idWk[ Γ' ])  ≈⟨ ✦'-map-pres-≈̇ (evalWk-pres-id Γ') ⟩
    ✦'-map id'[ evalCtx Γ' ]   ≈⟨ ✦'-map-pres-id' ⟩
    id'[ evalCtx Γ ]           ∎

  evalWk-pres-∘-π₁ : evalWk (drop[ a ] w) ≈̇ evalWk w ∘ π₁'[ evalTy a ]
  evalWk-pres-∘-π₁ = ≈̇-refl

  evalWk-pres-×-map-id : evalWk (keep[ a ] w) ≈̇ evalWk w ×'-map id'[ evalTy a ]
  evalWk-pres-×-map-id = ≈̇-refl

  evalWk-pres-π₁ : ∀ (Γ : Ctx) (a : Ty) → evalWk (fresh {Γ} {a}) ≈̇ π₁'[ evalTy a ]
  evalWk-pres-π₁ Γ a = let open EqReasoning (Sub'-setoid (Γ `, a) Γ) in begin
    evalWk (fresh {Γ} {a})              ≈⟨ ∘-pres-≈̇-left (evalWk-pres-id Γ) π₁'[ evalTy a ] ⟩
    id'[ evalCtx Γ ] ∘ π₁'[ evalTy a ]  ≈⟨ id'-unit-left (evalCtx Γ) π₁'[ evalTy a ] ⟩
    π₁'[ evalTy a ]                     ∎

  evalWk-pres-✦-map : evalWk (keep# w) ≈̇ ✦'-map (evalWk w)
  evalWk-pres-✦-map = ≈̇-refl

module _ {a : Ty} where
  abstract
    evalVar-pres-∘ : ∀ (w : Γ ⊆ Δ) (n : Var Γ a) → evalVar (wkVar w n) ≈̇ evalVar n ∘ evalWk w
    evalVar-pres-∘ (drop {Δ = Δ} {b} w) v = let open EqReasoning (Tm'-setoid (Δ `, b) a) in begin
      evalVar (wkVar (drop[ b ] w) v)                     ≈⟨ ∘-pres-≈̇-left (evalVar-pres-∘ w v) π₁'[ evalTy b ] ⟩
      (evalVar v ∘ evalWk w) ∘ π₁'[ evalTy b ]            ≈⟨ ∘-assoc (evalVar v) (evalWk w) π₁'[ evalTy b ] ⟩
      evalVar v ∘ evalWk (drop[ b ] w)                    ∎
    evalVar-pres-∘ (keep {Δ = Δ} {a} w) (ze {Γ}) = let open EqReasoning (Tm'-setoid (Δ `, a) a) in begin
      evalVar (wkVar (keep[ a ] w) (ze {Γ}))              ≈˘⟨ id'-unit-left (evalTy a) π₂'[ evalCtx Δ ] ⟩
      id'[ evalTy a ] ∘ π₂'[ evalCtx Δ ]                  ≈˘⟨ ×'-beta-right (evalWk w ∘ π₁'[ evalTy a ]) ⟩
      evalVar (ze {Γ} {a}) ∘ evalWk (keep[ a ] w)         ∎
    evalVar-pres-∘ (keep {Δ = Δ} {b} w) (su {Γ} {a} {b} n) = let open EqReasoning (Tm'-setoid (Δ `, b) a) in begin
      evalVar (wkVar (keep[ b ] w) (su {Γ} {a} {b} n))    ≈⟨ ∘-pres-≈̇-left (evalVar-pres-∘ w n) π₁'[ evalTy b ] ⟩
      (evalVar n ∘ evalWk w) ∘ π₁'[ evalTy b ]            ≈⟨ ∘-assoc (evalVar n) (evalWk w) π₁'[ evalTy b ] ⟩
      evalVar n ∘ evalWk w ∘ π₁'[ evalTy b ]              ≈˘⟨ ∘-pres-≈̇-right (evalVar n) (×'-beta-left (id' ∘ π₂')) ⟩
      evalVar n ∘ π₁'[ evalTy b ] ∘ evalWk (keep[ b ] w)  ≈˘⟨ ∘-assoc (evalVar n) π₁'[ evalTy b ] (evalWk (keep[ b ] w)) ⟩
      evalVar (su {Γ} {a} {b} n) ∘ evalWk (keep[ b ] w)   ∎
