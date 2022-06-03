{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Clouston.Evaluation.IS4.Base
  (Ctx' : Set₁)
  (let Ty' = Ctx')

  (_→̇_ : (P Q : Ctx') → Set) (let infixr 19 _→̇_; _→̇_ = _→̇_)

  (_≈̇_     : {P Q : Ctx'} → (φ ψ : P →̇ Q) → Set) (let infix 18 _≈̇_; _≈̇_ = _≈̇_)
  (≈̇-refl  : ∀ {P Q : Ctx'} {φ : P →̇ Q} → φ ≈̇ φ)
  (≈̇-sym   : ∀ {P Q : Ctx'} {φ ψ : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → ψ ≈̇ φ)
  (≈̇-trans : ∀ {P Q : Ctx'} {φ ψ ω : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → (ψ≈̇ω : ψ ≈̇ ω) → φ ≈̇ ω)

  (_∘_      : {P Q R : Ctx'} → (ψ : Q →̇ R) → (φ : P →̇ Q) → (P →̇ R)) (let infixr 19 _∘_; _∘_ = _∘_)
  (∘-pres-≈̇ : ∀ {P Q R : Ctx'} {ψ ψ' : Q →̇ R} {φ φ' : P →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ' ∘ φ')
  (∘-assoc  : {P Q R S : Ctx'} → (ω : R →̇ S) → (ψ : Q →̇ R) → (φ : P →̇ Q) → (ω ∘ ψ) ∘ φ ≈̇ ω ∘ ψ ∘ φ)

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

  (_⇒'_ : (P Q : Ty') → Ty')
  (lam' : {R P Q : Ty'} → (φ : R ×' P →̇ Q) → R →̇ P ⇒' Q)
  (app' : {R P Q : Ty'} → (φ : R →̇ P ⇒' Q) → (ψ : R →̇ P) → R →̇ Q)

  (✦'_             : (P : Ctx') → Ctx')
  (✦'-map_         : {P Q : Ctx'} → (φ : P →̇ Q) → ✦' P →̇ ✦' Q)
  (✦'-map-pres-≈̇   : {P Q : Ctx'} {φ φ' : P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → ✦'-map φ ≈̇ ✦'-map φ')
  (✦'-map-pres-id' : {P : Ctx'} → ✦'-map id'[ P ] ≈̇ id'[ ✦' P ])
  (η'[_]           : (P : Ctx') → P →̇ ✦' P)
  (μ'[_]           : (P : Ctx') → ✦' ✦' P →̇ ✦' P)

  (□'_  : (P : Ty') → Ty')
  (box' : {P Q : Ty'} → (φ : ✦' P →̇ Q) → P →̇ □' Q)
  (λ'   : {P Q : Ty'} → (φ : P →̇ □' Q) → ✦' P →̇ Q)
  where

open import IS4.Term.Base

import Semantics.Clouston.Evaluation.IML
  Ctx' _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ ∘-pres-≈̇ ∘-assoc id'[_] id'-unit-left id'-unit-right
  []' unit' []'-eta _×'_ ⟨_,_⟩' ⟨,⟩'-pres-≈̇ π₁'[_] π₂'[_] ×'-beta-left ×'-beta-right ×'-eta ⟨,⟩'-nat
  _⇒'_
  ✦'_ ✦'-map_ ✦'-map-pres-≈̇ ✦'-map-pres-id'
  □'_
  as CloustonEvaluationIML

open CloustonEvaluationIML public hiding (module Eval)

private
  η' = λ {P} → η'[ P ]

  μ' = λ {P} → μ'[ P ]

  unbox' : {R P Q : Ty'} → (φ : P →̇ □' Q) → (ψ : R →̇ ✦' P) → R →̇ Q
  unbox' φ ψ = λ' φ ∘ ψ

module Eval (N : Ty') where
  module CloustonEvaluationIMLEval = CloustonEvaluationIML.Eval N

  open CloustonEvaluationIMLEval public

  evalAcc : (e : CExt Γ ΓL ΓR) → evalCtx Γ →̇ ✦' evalCtx ΓL
  evalAcc nil             = η'
  evalAcc (ext {a = a} e) = evalAcc e ∘ π₁'[ evalTy a ]
  evalAcc (ext🔒- e)       = μ' ∘ ✦'-map (evalAcc e)
  
  evalTm : (t : Tm Γ a) → evalCtx Γ →̇ evalTy a
  evalTm (var v)     = evalVar v
  evalTm (lam t)     = lam' (evalTm t)
  evalTm (app t u)   = app' (evalTm t) (evalTm u)
  evalTm (box t)     = box' (evalTm t)
  evalTm (unbox t e) = unbox' (evalTm t) (evalAcc e)
  
  evalSub : (σ : Sub Δ Γ) → evalCtx Δ →̇ evalCtx Γ
  evalSub []         = unit'
  evalSub (σ `, t)   = ⟨ evalSub σ , evalTm t ⟩'
  evalSub (lock σ e) = ✦'-map (evalSub σ) ∘ evalAcc e
