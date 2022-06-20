{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Clouston.Evaluation.IML.Base
  (Ctx' : Set₁)

  (_→̇_ : (P Q : Ctx') → Set) (let infixr 19 _→̇_; _→̇_ = _→̇_)

  (_≈̇_     : {P Q : Ctx'} → (φ ψ : P →̇ Q) → Set) (let infix 18 _≈̇_; _≈̇_ = _≈̇_)
  (≈̇-refl  : ∀ {P Q : Ctx'} {φ : P →̇ Q} → φ ≈̇ φ)
  (≈̇-sym   : ∀ {P Q : Ctx'} {φ ψ : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → ψ ≈̇ φ)
  (≈̇-trans : ∀ {P Q : Ctx'} {φ ψ ω : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → (ψ≈̇ω : ψ ≈̇ ω) → φ ≈̇ ω)

  (_∘_ : {P Q R : Ctx'} → (ψ : Q →̇ R) → (φ : P →̇ Q) → (P →̇ R)) (let infixr 19 _∘_; _∘_ = _∘_)
  (let _[_]' = _∘_)

  (id'[_] : (P : Ctx') → P →̇ P)

  ([]'   : Ctx')
  (unit' : {P : Ctx'} → P →̇ []')

  (_×'_   : (P Q : Ctx') → Ctx')
  (⟨_,_⟩' : {R P Q : Ctx'} → (φ : R →̇ P) → (ψ : R →̇ Q) → R →̇ P ×' Q)
  (π₁'[_] : {P : Ctx'} → (Q : Ctx') → P ×' Q →̇ P)
  (π₂'[_] : (P : Ctx') → {Q : Ctx'} → P ×' Q →̇ Q)
  (let fst'[_]_ = λ {R} {P} Q φ → _∘_ {R} {P ×' Q} {P} π₁'[ Q ] φ)
  (let snd'[_]_ = λ {R} P {Q} φ → _∘_ {R} {P ×' Q} {Q} π₂'[ P ] φ)
  (let _×'-map_ = λ {P} {P'} {Q} {Q'} φ ψ → ⟨_,_⟩' {P ×' Q} {P'} {Q'} (φ ∘ π₁'[ Q ]) (ψ ∘ π₂'[ P ]))

  (let Ty' = Ctx')

  (_⇒'_ : (P Q : Ty') → Ty')
  (lam' : {R P Q : Ty'} → (φ : R ×' P →̇ Q) → R →̇ P ⇒' Q)
  (app' : {R P Q : Ty'} → (φ : R →̇ P ⇒' Q) → (ψ : R →̇ P) → R →̇ Q)

  (✦'_     : (P : Ctx') → Ctx')
  (✦'-map_ : {P Q : Ctx'} → (φ : P →̇ Q) → ✦' P →̇ ✦' Q)

  (□'_  : (P : Ty') → Ty')
  (box' : {P Q : Ty'} → (φ : ✦' P →̇ Q) → P →̇ □' Q)
  (λ'   : {P Q : Ty'} → (φ : P →̇ □' Q) → ✦' P →̇ Q)
  where

open import Level using (0ℓ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Type
open import Context Ty Ty-Decidable

-- XXX: make parameters
≈̇-equiv : ∀ (P Q : Ctx') → IsEquivalence (_≈̇_ {P} {Q})
≈̇-equiv  P Q = record { refl = ≈̇-refl {P} {Q} ; sym = ≈̇-sym {P} {Q} ; trans = ≈̇-trans {P} {Q} }

→̇-setoid : (P Q : Ctx') → Setoid 0ℓ 0ℓ
→̇-setoid P Q = record { Carrier = P →̇ Q ; _≈_ = _≈̇_ ; isEquivalence = ≈̇-equiv P Q }

id' = λ {P} → id'[ P ]

π₁'       = λ {P} {Q} → π₁'[_] {P} Q
π₁'[_][_] = λ P Q → π₁'[_] {P} Q

π₂'       = λ {P} {Q} → π₂'[_] P {Q}
π₂'[_][_] = λ P Q → π₂'[_] P {Q}

-- Δ' : {P P : Ctx'} → P →̇ P ×' P

unbox' : {R P Q : Ty'} → (φ : P →̇ □' Q) → (ψ : R →̇ ✦' P) → R →̇ Q
unbox' φ ψ = λ' φ ∘ ψ

module Eval (N : Ty') where
  evalTy : (a : Ty) → Ty'
  evalTy 𝕓       = N
  evalTy (a ⇒ b) = evalTy a ⇒' evalTy b
  evalTy (□ a)   = □' evalTy a

  evalCtx : (Γ : Ctx) → Ty'
  evalCtx []       = []'
  evalCtx (Γ `, a) = evalCtx Γ ×' evalTy a
  evalCtx (Γ 🔒)    = ✦' evalCtx Γ

  evalWk : (w : Γ ⊆ Δ) → evalCtx Δ →̇ evalCtx Γ
  evalWk base             = unit'
  evalWk (drop {a = a} w) = evalWk w ∘ π₁'[ evalTy a ]
  evalWk (keep {a = a} w) = evalWk w ×'-map id'[ evalTy a ]
  evalWk (keep🔒 w)        = ✦'-map (evalWk w)

  evalVar : (v : Var Γ a) → evalCtx Γ →̇ evalTy a
  evalVar (ze {Γ})       = π₂'[ evalCtx Γ ]
  evalVar (su {b = b} v) = evalVar v ∘ π₁'[ evalTy b ]

  Sub' = λ Δ Γ → evalCtx Δ →̇ evalCtx Γ

  Sub'-setoid = λ Δ Γ → →̇-setoid (evalCtx Δ) (evalCtx Γ)

  Tm' = λ Γ a → evalCtx Γ →̇ evalTy a

  Tm'-setoid = λ Γ a → →̇-setoid (evalCtx Γ) (evalTy a)
