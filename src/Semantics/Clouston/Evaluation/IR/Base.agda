{-# OPTIONS --safe --without-K #-}
module Semantics.Clouston.Evaluation.IR.Base
  (Ctx' : Set₁)
  (let Ty' = Ctx')

  (_→̇_ : (P Q : Ctx') → Set) (let infixr 19 _→̇_; _→̇_ = _→̇_)

  (_≈̇_     : {P Q : Ctx'} → (φ ψ : P →̇ Q) → Set) (let infix 18 _≈̇_; _≈̇_ = _≈̇_)
  (≈̇-refl  : ∀ {P Q : Ctx'} {φ : P →̇ Q} → φ ≈̇ φ)
  (≈̇-sym   : ∀ {P Q : Ctx'} {φ ψ : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → ψ ≈̇ φ)
  (≈̇-trans : ∀ {P Q : Ctx'} {φ ψ ω : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → (ψ≈̇ω : ψ ≈̇ ω) → φ ≈̇ ω)

  (_∘_ : {P Q R : Ctx'} → (ψ : Q →̇ R) → (φ : P →̇ Q) → (P →̇ R)) (let infixr 19 _∘_; _∘_ = _∘_)

  (id'[_] : (P : Ctx') → P →̇ P)

  ([]'   : Ctx')
  (unit' : {P : Ctx'} → P →̇ []')

  (_×'_   : (P Q : Ctx') → Ctx')
  (⟨_,_⟩' : {R P Q : Ctx'} → (φ : R →̇ P) → (ψ : R →̇ Q) → R →̇ P ×' Q)
  (π₁'[_] : {P : Ctx'} → (Q : Ctx') → P ×' Q →̇ P)
  (π₂'[_] : (P : Ctx') → {Q : Ctx'} → P ×' Q →̇ Q)
  (let fst'[_]_ = λ {R} {P} Q φ → _∘_ {R} {P ×' Q} {P} π₁'[ Q ] φ)
  (let snd'[_]_ = λ {R} P {Q} φ → _∘_ {R} {P ×' Q} {Q} π₂'[ P ] φ)

  (_⇒'_ : (P Q : Ty') → Ty')
  (lam' : {R P Q : Ty'} → (φ : R ×' P →̇ Q) → R →̇ P ⇒' Q)
  (app' : {R P Q : Ty'} → (φ : R →̇ P ⇒' Q) → (ψ : R →̇ P) → R →̇ Q)

  (✦'_     : (P : Ctx') → Ctx')
  (✦'-map_ : {P Q : Ctx'} → (φ : P →̇ Q) → ✦' P →̇ ✦' Q)
  (ε'[_]   : (P : Ctx') → ✦' P →̇ P)

  (□'_  : (P : Ty') → Ty')
  (box' : {P Q : Ty'} → (φ : ✦' P →̇ Q) → P →̇ □' Q)
  (λ'   : {P Q : Ty'} → (φ : P →̇ □' Q) → ✦' P →̇ Q)
  where

open import IR.Term

import Semantics.Clouston.Evaluation.IML.Base
  Ctx' _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ id'[_]
  []' unit' _×'_ ⟨_,_⟩' π₁'[_] π₂'[_]
  _⇒'_ lam' app'
  ✦'_ ✦'-map_
  □'_ box' λ'
  as CloustonEvaluationIMLBase

open CloustonEvaluationIMLBase public hiding (module Eval)

-- XXX: make parameter
ε' = λ {P} → ε'[ P ]

module Eval (N : Ty') where
  module CloustonEvaluationIMLEval = CloustonEvaluationIMLBase.Eval N

  open CloustonEvaluationIMLEval public hiding (evalWk ; evalVar)

  evalAcc : (e : Ext Γ Δ) → evalCtx Δ →̇ ✦' evalCtx Γ
  evalAcc new[ Γ ]     = id'[ ✦' evalCtx Γ ]
  evalAcc (ext[ a ] e) = evalAcc e ∘ π₁'[ evalTy a ]
  evalAcc (ext#- e)    = evalAcc e ∘ ε'

  evalVar : (v : Var Γ a) → evalCtx Γ →̇ evalTy a
  evalVar zero      = π₂'
  evalVar (succ  v) = evalVar v ∘ π₁'
  evalVar (succ# v) = evalVar v ∘ ε'

  evalRen : (r : Ren Δ Γ) → evalCtx Δ →̇ evalCtx Γ
  evalRen []         = unit'
  evalRen (r `, v)   = ⟨ evalRen r , evalVar v ⟩'
  evalRen (lock r e) = ✦'-map evalRen r ∘ evalAcc e

  evalTm : (t : Tm Γ a) → evalCtx Γ →̇ evalTy a
  evalTm (var v)   = evalVar v
  evalTm (lam t)   = lam' (evalTm t)
  evalTm (app t u) = app' (evalTm t) (evalTm u)
  evalTm (box t)   = box' (evalTm t)
  evalTm (unb t e) = unbox' (evalTm t) (evalAcc e)
  
  evalSub : (σ : Sub Δ Γ) → evalCtx Δ →̇ evalCtx Γ
  evalSub []         = unit'
  evalSub (σ `, t)   = ⟨ evalSub σ , evalTm t ⟩'
  evalSub (lock σ e) = ✦'-map (evalSub σ) ∘ evalAcc e
