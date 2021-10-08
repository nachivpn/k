open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Clouston.Evaluation.IS4.Properties
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

  (N : Ty')
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import IS4.Term

open import Semantics.Clouston.Evaluation.IS4.Base
    Ctx' _→̇_ _≈̇_ ≈̇-refl ≈̇-sym ≈̇-trans _∘_ ∘-pres-≈̇ ∘-assoc id'[_] id'-unit-left id'-unit-right
    []' unit' []'-eta _×'_ ⟨_,_⟩' ⟨,⟩'-pres-≈̇ π₁'[_] π₂'[_] ×'-beta-left ×'-beta-right ×'-eta ⟨,⟩'-nat
    _⇒'_ lam' app'
    ✦'_ ✦'-map_ ✦'-map-pres-≈̇ ✦'-map-pres-id' η'[_] μ'[_]
    □'_ box' λ'
  renaming (module Eval to CloustonEvaluationIS4BaseEval)

open CloustonEvaluationIS4BaseEval N

-- XXX: make parameters
private
  unbox' : {R P Q : Ty'} → (φ : P →̇ □' Q) → (ψ : R →̇ ✦' P) → R →̇ Q
  unbox' φ ψ = λ' φ ∘ ψ

  η' = λ {P} → η'[ P ]

  μ' = λ {P} → μ'[ P ]

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
  evalAcc-pres-id : ∀ (Γ : Ctx) → evalAcc new[ Γ ] ≈̇ id'[ ✦' evalCtx Γ ]
  evalAcc-pres-id Γ = η'-unit-right[ evalCtx Γ ]

module _ {Δ Γ : Ctx} where
  abstract
    evalAcc-pres-∘ : ∀ (e : CExt Δ Γ Γ') (e' : CExt Θ Δ Δ') → evalAcc (extRAssoc e e') ≈̇ μ'[ evalCtx Γ ] ∘ ✦'-map (evalAcc e) ∘ evalAcc e'
    evalAcc-pres-∘ {Θ = Δ} e nil = let open EqReasoning (Sub'-setoid Δ (Γ 🔒)) in begin
      evalAcc (extRAssoc e (nil {Γ = Δ}))
        ≡⟨⟩
      evalAcc e
        ≈˘⟨ id'-unit-left (✦' evalCtx Γ) (evalAcc e) ⟩
      id'[ ✦' evalCtx Γ ] ∘ evalAcc e
        ≈˘⟨ ∘-pres-≈̇-left η'-unit-left[ evalCtx Γ ] (evalAcc e) ⟩
      (μ'[ evalCtx Γ ] ∘ η'[ ✦' evalCtx Γ ]) ∘ evalAcc e
        ≈⟨ ∘-assoc μ'[ evalCtx Γ ] η'[ ✦' evalCtx Γ ] (evalAcc e) ⟩
      μ'[ evalCtx Γ ] ∘ η'[ ✦' evalCtx Γ ] ∘ evalAcc e
        ≈˘⟨ ∘-pres-≈̇-right μ'[ evalCtx Γ ] (η'-nat (evalAcc e)) ⟩
      μ'[ evalCtx Γ ] ∘ ✦'-map (evalAcc e) ∘ evalAcc (nil {Γ = Δ})
        ∎
    evalAcc-pres-∘ {Θ = Θ `, a} e (ext {a = a} e') = let open EqReasoning (Sub'-setoid (Θ `, a) (Γ 🔒)) in begin
      evalAcc (extRAssoc e (ext {a = a} e'))
        ≡⟨⟩
      evalAcc (ext {a = a} (extRAssoc e e'))
        ≡⟨⟩
      evalAcc (extRAssoc e e') ∘ π₁'[ evalCtx Θ ][ evalTy a ]
        ≈⟨ ∘-pres-≈̇-left (evalAcc-pres-∘ e e') π₁'[ evalCtx Θ ][ evalTy a ] ⟩
      (μ'[ evalCtx Γ ] ∘ ✦'-map (evalAcc e) ∘ evalAcc e') ∘ π₁'[ evalCtx Θ ][ evalTy a ]
        ≈⟨ ∘-assoc μ'[ evalCtx Γ ] (✦'-map (evalAcc e) ∘ evalAcc e') π₁'[ evalCtx Θ ][ evalTy a ] ⟩
      μ'[ evalCtx Γ ] ∘ (✦'-map (evalAcc e) ∘ evalAcc e') ∘ π₁'[ evalCtx Θ ][ evalTy a ]
        ≈⟨ ∘-pres-≈̇-right μ'[ evalCtx Γ ] (∘-assoc (✦'-map (evalAcc e)) (evalAcc e') π₁'[ evalCtx Θ ][ evalTy a ]) ⟩
      μ'[ evalCtx Γ ] ∘ ✦'-map (evalAcc e) ∘ evalAcc (ext {a = a} e')
        ∎
    evalAcc-pres-∘ {Θ = Θ 🔒} e (ext🔒- e') = let open EqReasoning (Sub'-setoid (Θ 🔒) (Γ 🔒)) in begin
      evalAcc (extRAssoc e (ext🔒- e'))
        ≡⟨⟩
      evalAcc (ext🔒- (extRAssoc e e'))
        ≡⟨⟩
      μ'[ evalCtx Γ ] ∘ ✦'-map (evalAcc (extRAssoc e e'))
        ≈⟨ ∘-pres-≈̇-right μ'[ evalCtx Γ ] (✦'-map-pres-≈̇ (evalAcc-pres-∘ e e')) ⟩
      μ'[ evalCtx Γ ] ∘ ✦'-map (μ'[ evalCtx Γ ] ∘ ✦'-map (evalAcc e) ∘ evalAcc e')
        ≈⟨ ∘-pres-≈̇-right μ'[ evalCtx Γ ] (✦'-map-pres-∘ μ'[ evalCtx Γ ] (✦'-map (evalAcc e) ∘ evalAcc e')) ⟩
      μ'[ evalCtx Γ ] ∘ ✦'-map μ'[ evalCtx Γ ] ∘ ✦'-map (✦'-map (evalAcc e) ∘ evalAcc e')
        ≈˘⟨ ∘-assoc μ' (✦'-map μ') (✦'-map (✦'-map (evalAcc e) ∘ evalAcc e')) ⟩
      (μ'[ evalCtx Γ ] ∘ ✦'-map μ'[ evalCtx Γ ]) ∘ ✦'-map (✦'-map (evalAcc e) ∘ evalAcc e')
        ≈⟨ ∘-pres-≈̇ (≈̇-sym μ'-assoc[ evalCtx Γ ]) (✦'-map-pres-∘ (✦'-map (evalAcc e)) (evalAcc e')) ⟩
      (μ'[ evalCtx Γ ] ∘ μ'[ ✦' evalCtx Γ ]) ∘ ✦'-map (✦'-map (evalAcc e)) ∘ ✦'-map (evalAcc e')
        ≈⟨ ∘-assoc μ' μ' (✦'-map ✦'-map (evalAcc e) ∘ ✦'-map (evalAcc e')) ⟩
      μ'[ evalCtx Γ ] ∘ μ'[ ✦' evalCtx Γ ] ∘ ✦'-map (✦'-map (evalAcc e)) ∘ ✦'-map (evalAcc e')
        ≈˘⟨ ∘-pres-≈̇-right μ' (∘-assoc μ' (✦'-map (✦'-map (evalAcc e))) (✦'-map (evalAcc e'))) ⟩
      μ'[ evalCtx Γ ] ∘ (μ'[ ✦' evalCtx Γ ] ∘ ✦'-map (✦'-map (evalAcc e))) ∘ ✦'-map (evalAcc e')
        ≈˘⟨ ∘-pres-≈̇-right μ' (∘-pres-≈̇-left (μ'-nat (evalAcc e)) (✦'-map (evalAcc e'))) ⟩
      μ'[ evalCtx Γ ] ∘ (✦'-map (evalAcc e) ∘ μ'[ evalCtx Δ ]) ∘ ✦'-map (evalAcc e')
        ≈⟨ ∘-pres-≈̇-right μ' (∘-assoc (✦'-map evalAcc e) μ' (✦'-map (evalAcc e'))) ⟩
      μ'[ evalCtx Γ ] ∘ ✦'-map (evalAcc e) ∘ evalAcc (ext🔒- e')
        ∎

module _ {ΓL : Ctx} where
  abstract
    acc-nat' : ∀ (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Δ) → evalAcc e ∘ evalWk w ≈̇ ✦'-map (evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w) -- XXX: rename and split up
    acc-nat' nil w = ≈̇-sym (η'-nat _)
    acc-nat' (ext {a = a} e) (keep {Δ = Δ} {a} w) = let open EqReasoning (Sub'-setoid (Δ `, a) (ΓL 🔒)) in begin
      evalAcc (ext {a = a} e) ∘ evalWk (keep {a = a} w)
        ≈⟨ ∘-assoc (evalAcc e) π₁' (evalWk (keep {a = a} w)) ⟩
      evalAcc e ∘ π₁'[ evalTy a ] ∘ evalWk (keep {a = a} w)
        ≈⟨ ∘-pres-≈̇-right (evalAcc e) (×'-beta-left (id'[ evalTy a ] ∘ π₂'[ evalCtx Δ ])) ⟩
      evalAcc e ∘ evalWk w ∘ π₁'[ evalTy a ]
        ≈˘⟨ ∘-assoc (evalAcc e) (evalWk w) (π₁'[ evalTy a ]) ⟩
      (evalAcc e ∘ evalWk w) ∘ π₁'[ evalTy a ]
        ≈⟨ ∘-pres-≈̇-left (acc-nat' e w) π₁'[ evalTy a ] ⟩
      (✦'-map (evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w)) ∘ π₁'[ evalTy a ]
        ≈⟨ ∘-assoc (✦'-map (evalWk (factor2≤ e w))) (evalAcc (factor2Ext e w)) π₁'[ evalTy a ] ⟩
      ✦'-map (evalWk (factor2≤ (ext {a = a} e) (keep {a = a} w))) ∘ evalAcc (factor2Ext (ext {a = a} e) (keep {a = a} w))
        ∎
    acc-nat' e@(ext {a = a} _) (drop {Δ = Δ} {b} w) = let open EqReasoning (Sub'-setoid (Δ `, b) (ΓL 🔒)) in begin
      evalAcc e ∘ evalWk (drop {Δ = Δ} {b} w)
        ≈˘⟨ ∘-assoc (evalAcc e) (evalWk w) π₁'[ evalTy b ] ⟩
      (evalAcc e ∘ evalWk w) ∘ π₁'[ evalTy b ]
        ≈⟨ ∘-pres-≈̇-left (acc-nat' e w) π₁'[ evalTy b ] ⟩
      (✦'-map (evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w)) ∘ π₁'[ evalTy b ]
        ≈⟨ ∘-assoc (✦'-map (evalWk (factor2≤ e w))) (evalAcc (factor2Ext e w)) π₁'[ evalTy b ] ⟩
      ✦'-map (evalWk (factor2≤ e (drop {Δ = Δ} {b} w))) ∘ evalAcc (factor2Ext e (drop {Δ = Δ} {b} w))
        ∎
    acc-nat' (ext🔒- e) (keep🔒 {Δ = Δ} w) = let open EqReasoning (Sub'-setoid (Δ 🔒) (ΓL 🔒)) in begin
      evalAcc (ext🔒- e) ∘ evalWk (keep🔒 w)
        ≈⟨ ∘-assoc μ' (✦'-map (evalAcc e)) (✦'-map (evalWk w)) ⟩
      μ' ∘ ✦'-map (evalAcc e) ∘ ✦'-map (evalWk w)
        ≈˘⟨ ∘-pres-≈̇-right μ' (✦'-map-pres-∘ (evalAcc e) (evalWk w)) ⟩
      μ' ∘ ✦'-map (evalAcc e ∘ evalWk w)
        ≈⟨ ∘-pres-≈̇-right μ' (✦'-map-pres-≈̇ (acc-nat' e w)) ⟩
      μ' ∘ ✦'-map (✦'-map (evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w))
        ≈⟨ ∘-pres-≈̇-right μ' (✦'-map-pres-∘ (✦'-map (evalWk (factor2≤ e w))) (evalAcc (factor2Ext e w))) ⟩
      μ' ∘ ✦'-map (✦'-map (evalWk (factor2≤ e w))) ∘ ✦'-map (evalAcc (factor2Ext e w))
        ≈˘⟨ ∘-assoc μ' (✦'-map (✦'-map (evalWk (factor2≤ e w)))) (✦'-map (evalAcc (factor2Ext e w))) ⟩
      (μ' ∘ ✦'-map (✦'-map (evalWk (factor2≤ e w)))) ∘ ✦'-map (evalAcc (factor2Ext e w))
        ≈˘⟨ ∘-pres-≈̇-left (μ'-nat (evalWk (factor2≤ e w))) (✦'-map (evalAcc (factor2Ext e w))) ⟩
      (✦'-map (evalWk (factor2≤ e w)) ∘ μ') ∘ ✦'-map (evalAcc (factor2Ext e w))
        ≈⟨ ∘-assoc (✦'-map (evalWk (factor2≤ e w))) μ' (✦'-map (evalAcc (factor2Ext e w))) ⟩
      ✦'-map (evalWk (factor2≤ (ext🔒- e) (keep🔒 w))) ∘ evalAcc (factor2Ext (ext🔒- e) (keep🔒 w))
        ∎
    acc-nat' e@(ext🔒- _) (drop {Δ = Δ} {a} w) = let open EqReasoning (Sub'-setoid (Δ `, a) (ΓL 🔒)) in begin
      evalAcc e ∘ evalWk (drop {Δ = Δ} {a} w)
        ≈˘⟨ ∘-assoc (evalAcc e) (evalWk w) π₁'[ evalTy a ] ⟩
      (evalAcc e ∘ evalWk w) ∘ π₁'[ evalTy a ]
        ≈⟨ ∘-pres-≈̇-left (acc-nat' e w) π₁'[ evalTy a ] ⟩
      (✦'-map (evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w)) ∘ π₁'[ evalTy a ]
        ≈⟨ ∘-assoc (✦'-map (evalWk (factor2≤ e w))) (evalAcc (factor2Ext e w)) π₁'[ evalTy a ] ⟩
      ✦'-map (evalWk (factor2≤ e (drop {Δ = Δ} {a} w))) ∘ evalAcc (factor2Ext e (drop {Δ = Δ} {a} w))
        ∎

module _ {ΓL : Ctx} where
  abstract
     acc-nat : ∀ (e : CExt Γ ΓL ΓR) (σ : Sub Δ Γ) → evalAcc e ∘ evalSub σ ≈̇ ✦'-map (evalSub (factor2Sub e σ)) ∘ evalAcc (factor2Extₛ e σ) -- XXX: rename and split up
     acc-nat nil σ = ≈̇-sym (η'-nat (evalSub σ))
     acc-nat {Δ = Δ} (ext {a = a} e) (σ `, t) = let open EqReasoning (Sub'-setoid Δ (ΓL 🔒)) in begin
       evalAcc (ext {a = a} e) ∘ (evalSub (σ `, t))
         ≡⟨⟩
       (evalAcc e ∘ π₁'[ evalTy a ]) ∘ ⟨ evalSub σ , evalTm t ⟩'
         ≈⟨ ∘-assoc (evalAcc e) π₁'[ evalTy a ] ⟨ evalSub σ , evalTm t ⟩' ⟩
       evalAcc e ∘ π₁'[ evalTy a ] ∘ ⟨ evalSub σ , evalTm t ⟩'
         ≈⟨ ∘-pres-≈̇-right (evalAcc e) (×'-beta-left (evalTm t)) ⟩
       evalAcc e ∘ evalSub σ
         ≈⟨ acc-nat e σ ⟩
       ✦'-map (evalSub (factor2Sub e σ)) ∘ evalAcc (factor2Extₛ e σ)
         ≡⟨⟩
       ✦'-map (evalSub (factor2Sub (ext {a = a} e) (σ `, t))) ∘ evalAcc (factor2Extₛ (ext {a = a} e) (σ `, t))
         ∎
     acc-nat {Δ = Δ} (ext🔒- e) (lock σ e') = let open EqReasoning (Sub'-setoid Δ (ΓL 🔒)) in begin
       evalAcc (ext🔒- e) ∘ evalSub (lock σ e')
         ≡⟨⟩
       (μ' ∘ ✦'-map (evalAcc e)) ∘ ✦'-map (evalSub σ) ∘ evalAcc e'
         ≈⟨ ∘-assoc μ' (✦'-map (evalAcc e)) (✦'-map (evalSub σ) ∘ evalAcc e') ⟩
       μ' ∘ ✦'-map (evalAcc e) ∘ ✦'-map (evalSub σ) ∘ evalAcc e'
         ≈˘⟨ ∘-pres-≈̇-right μ' (∘-assoc (✦'-map (evalAcc e)) (✦'-map (evalSub σ)) (evalAcc e')) ⟩
       μ' ∘ (✦'-map (evalAcc e) ∘ ✦'-map (evalSub σ)) ∘ evalAcc e'
         ≈˘⟨ ∘-pres-≈̇-right μ' (∘-pres-≈̇-left (✦'-map-pres-∘ (evalAcc e) (evalSub σ)) (evalAcc e')) ⟩
       μ' ∘ ✦'-map (evalAcc e ∘ evalSub σ) ∘ evalAcc e'
         ≈⟨ ∘-pres-≈̇-right μ' (∘-pres-≈̇-left (✦'-map-pres-≈̇ (acc-nat e σ)) (evalAcc e')) ⟩
       μ' ∘ ✦'-map (✦'-map (evalSub (factor2Sub e σ)) ∘ evalAcc (factor2Extₛ e σ)) ∘ evalAcc e'
         ≈⟨ ∘-pres-≈̇-right μ' (∘-pres-≈̇-left (✦'-map-pres-∘ (✦'-map (evalSub (factor2Sub e σ))) (evalAcc (factor2Extₛ e σ))) (evalAcc e')) ⟩
       μ' ∘ (✦'-map ✦'-map (evalSub (factor2Sub e σ)) ∘ ✦'-map (evalAcc (factor2Extₛ e σ))) ∘ evalAcc e'
         ≈⟨ ∘-pres-≈̇-right μ' (∘-assoc (✦'-map ✦'-map (evalSub (factor2Sub e σ))) (✦'-map (evalAcc (factor2Extₛ e σ))) (evalAcc e')) ⟩
       μ' ∘ ✦'-map ✦'-map (evalSub (factor2Sub e σ)) ∘ ✦'-map (evalAcc (factor2Extₛ e σ)) ∘ evalAcc e'
         ≈˘⟨ ∘-assoc μ' (✦'-map ✦'-map evalSub (factor2Sub e σ)) (✦'-map (evalAcc (factor2Extₛ e σ)) ∘ evalAcc e') ⟩
       (μ' ∘ ✦'-map ✦'-map (evalSub (factor2Sub e σ))) ∘ ✦'-map (evalAcc (factor2Extₛ e σ)) ∘ evalAcc e'
         ≈˘⟨ ∘-pres-≈̇-left (μ'-nat (evalSub (factor2Sub e σ))) (✦'-map (evalAcc (factor2Extₛ e σ)) ∘ evalAcc e') ⟩
       (✦'-map (evalSub (factor2Sub e σ)) ∘ μ') ∘ ✦'-map (evalAcc (factor2Extₛ e σ)) ∘ evalAcc e'
         ≈⟨ ∘-assoc (✦'-map (evalSub (factor2Sub e σ))) μ' (✦'-map (evalAcc (factor2Extₛ e σ)) ∘ evalAcc e') ⟩
       ✦'-map (evalSub (factor2Sub e σ)) ∘ μ' ∘ ✦'-map (evalAcc (factor2Extₛ e σ)) ∘ evalAcc e'
         ≈˘⟨ ∘-pres-≈̇-right (✦'-map (evalSub (factor2Sub e σ))) (evalAcc-pres-∘ (factor2Extₛ e σ) e') ⟩
       ✦'-map (evalSub (factor2Sub (ext🔒- e) (lock σ e'))) ∘ evalAcc (extRAssoc (factor2Extₛ e σ) e')
         ∎

abstract
  evalTm-pres-∘' : ∀ (w : Γ ⊆ Δ) (t : Tm Γ a) → evalTm (wkTm w t) ≈̇ evalTm t [ evalWk w ]'
  evalTm-pres-∘' w (var v) = evalVar-pres-∘ w v
  evalTm-pres-∘' {Δ = Δ} {a} w (lam {a = a'} t) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (lam t))
      ≈⟨ lam'-pres-≈̇ (evalTm-pres-∘' (keep {a = a'} w) t) ⟩
    lam' (evalTm t ∘ evalWk (keep {a = a'} w))
      ≈˘⟨ lam'-nat (evalTm t) (evalWk w) ⟩
    evalTm (lam t) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (app t u) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (app t u))
      ≈⟨ app'-pres-≈̇ (evalTm-pres-∘' w t) (evalTm-pres-∘' w u) ⟩
    app' (evalTm t ∘ evalWk w) (evalTm u ∘ evalWk w)
      ≈˘⟨ app'-nat (evalTm t) (evalTm u) (evalWk w) ⟩
    evalTm (app t u) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (box t) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (box t))
      ≈⟨ box'-pres-≈̇ (evalTm-pres-∘' (keep🔒 w) t) ⟩
    box' (evalTm t ∘ evalWk (keep🔒 w))
      ≈⟨ box'-nat-dom (evalTm t) (evalWk w) ⟩
    evalTm (box t) [ evalWk w ]'
      ∎
  evalTm-pres-∘' {Δ = Δ} {a} w (unbox t e) = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (wkTm w (unbox t e))
      ≈⟨ unbox'-pres-≈̇-left (evalTm-pres-∘' (factor2≤ e w) t) (evalAcc (factor2Ext e w)) ⟩
    unbox' (evalTm t ∘ evalWk (factor2≤ e w)) (evalAcc (factor2Ext e w))
      ≈⟨ unbox'-nat-dom (evalTm t) (evalWk (factor2≤ e w)) (evalAcc (factor2Ext e w)) ⟩
    unbox' (evalTm t) (✦'-map (evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w))
      ≈˘⟨ unbox'-pres-≈̇-right (evalTm t) (acc-nat' e w) ⟩
    unbox' (evalTm t) (evalAcc e ∘ evalWk w)
      ≈˘⟨ ∘-assoc (λ' (evalTm t)) (evalAcc e) (evalWk w) ⟩
    evalTm (unbox t e) [ evalWk w ]'
      ∎

abstract
  evalSub-pres-∘' : ∀ (σ : Sub Δ Γ) (w : Δ ⊆ Δ') → evalSub (wkSub w σ) ≈̇ evalSub σ ∘ evalWk w
  evalSub-pres-∘' []         w = ≈̇-sym []'-eta
  evalSub-pres-∘' {Γ = Γ} {Δ'} (σ `, t)   w = let open EqReasoning (Sub'-setoid Δ' Γ) in begin
    evalSub (wkSub w (σ `, t))
      ≈⟨ ⟨,⟩'-pres-≈̇ (evalSub-pres-∘' σ w) (evalTm-pres-∘' w t) ⟩
    ⟨ evalSub σ ∘ evalWk w , evalTm t ∘ evalWk w ⟩'
      ≈˘⟨ ⟨,⟩'-nat (evalSub σ) (evalTm t) (evalWk w) ⟩
    evalSub (σ `, t) ∘ evalWk w
      ∎
  evalSub-pres-∘' {Γ = Γ} {Δ'} (lock σ e) w = let open EqReasoning (Sub'-setoid Δ' Γ) in begin
    evalSub (wkSub w (lock σ e))
      ≈⟨ ∘-pres-≈̇-left (✦'-map-pres-≈̇ (evalSub-pres-∘' σ (factor2≤ e w))) (evalAcc (factor2Ext e w)) ⟩
    ✦'-map (evalSub σ ∘ evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w)
      ≈⟨ ∘-pres-≈̇-left (✦'-map-pres-∘ (evalSub σ) (evalWk (factor2≤ e w))) (evalAcc (factor2Ext e w)) ⟩
    (✦'-map (evalSub σ) ∘ ✦'-map (evalWk (factor2≤ e w))) ∘ evalAcc (factor2Ext e w)
      ≈⟨ ∘-assoc (✦'-map (evalSub σ)) (✦'-map (evalWk (factor2≤ e w))) (evalAcc (factor2Ext e w)) ⟩
    ✦'-map (evalSub σ) ∘ ✦'-map (evalWk (factor2≤ e w)) ∘ evalAcc (factor2Ext e w)
      ≈˘⟨ ∘-pres-≈̇-right (✦'-map (evalSub σ)) (acc-nat' e w) ⟩
    ✦'-map (evalSub σ) ∘ evalAcc e ∘ evalWk w
      ≈˘⟨ ∘-assoc (✦'-map (evalSub σ)) (evalAcc e) (evalWk w) ⟩
    evalSub (lock σ e) ∘ evalWk w
      ∎

abstract
  evalSub-pres-∘-π₁ : ∀ (σ : Sub Δ Γ) (a : Ty) → evalSub (dropₛ {Δ} {Γ} {a} σ) ≈̇ evalSub σ ∘ π₁'[ evalTy a ]
  evalSub-pres-∘-π₁ {Δ} {Γ} σ a = let open EqReasoning (Sub'-setoid (Δ `, a) Γ) in begin
    evalSub (dropₛ {Δ} {Γ} {a} σ)       ≈⟨ evalSub-pres-∘' σ (fresh {Δ} {a}) ⟩
    evalSub σ ∘ evalWk (fresh {Δ} {a})  ≈⟨ ∘-pres-≈̇-right (evalSub σ) (evalWk-pres-π₁ Δ a) ⟩
    evalSub σ ∘ π₁'[ evalTy a ]         ∎

abstract
  evalSub-pres-×-map-id : ∀ (σ : Sub Δ Γ) (a : Ty) → evalSub (keepₛ {Δ} {Γ} {a} σ) ≈̇ evalSub σ ×'-map id'[ evalTy a ]
  evalSub-pres-×-map-id {Δ} {Γ} σ a = let open EqReasoning (Sub'-setoid (Δ `, a) (Γ `, a)) in begin
    evalSub (keepₛ {Δ} {Γ} {a} σ)    ≈⟨ ⟨,⟩'-pres-≈̇ (evalSub-pres-∘-π₁ σ a) (≈̇-sym (id'-unit-left (evalTy a) π₂'[ evalCtx Δ ])) ⟩
    evalSub σ ×'-map id'[ evalTy a ]  ∎

abstract
  evalSub-pres-lock-map : ∀ (σ : Sub Δ Γ) → evalSub (keep🔒ₛ σ) ≈̇ ✦'-map (evalSub σ)
  evalSub-pres-lock-map {Δ} {Γ} σ = let open EqReasoning (Sub'-setoid (Δ 🔒) (Γ 🔒)) in begin
    evalSub (keep🔒ₛ σ)                      ≈⟨ ∘-pres-≈̇-right (✦'-map (evalSub σ)) (evalAcc-pres-id Δ) ⟩
    ✦'-map (evalSub σ) ∘ id'[ ✦' evalCtx Δ ]  ≈⟨ id'-unit-right (✦' evalCtx Δ) (✦'-map (evalSub σ)) ⟩
    ✦'-map (evalSub σ)                       ∎

abstract
  evalSub-pres-wk : ∀ (w : Γ ⊆ Γ') → evalSub (embWk w) ≈̇ evalWk w
  evalSub-pres-wk base = []'-eta
  evalSub-pres-wk {Γ} (drop {Δ = Γ'} {a} w) = let open EqReasoning (Sub'-setoid (Γ' `, a) Γ) in begin
    evalSub (embWk (drop {a = a} w))             ≈⟨ evalSub-pres-∘' (embWk w) (fresh {Γ'} {a}) ⟩
    evalSub (embWk w) ∘ evalWk (fresh {Γ'} {a})  ≈⟨ ∘-pres-≈̇ (evalSub-pres-wk w) (evalWk-pres-π₁ Γ' a) ⟩
    evalWk (drop {a = a} w)                      ∎
  evalSub-pres-wk {Γ} (keep {Δ = Γ'} {a} w) = let open EqReasoning (Sub'-setoid (Γ' `, a) Γ) in begin
    evalSub (embWk (keep {Δ = Γ'} {a} w))        ≈⟨ evalSub-pres-×-map-id (embWk w) a ⟩
    evalSub (embWk w) ×'-map id'[ evalTy a ]      ≈⟨ ×'-map-pres-≈̇-left (evalSub-pres-wk w) id' ⟩
    evalWk (keep {Δ = Γ'} {a} w)                 ∎
  evalSub-pres-wk {Γ} (keep🔒 {Δ = Γ'} w) = let open EqReasoning (Sub'-setoid (Γ' 🔒) Γ) in begin
    evalSub (embWk (keep🔒 w))                   ≈⟨ evalSub-pres-lock-map (embWk w) ⟩
    ✦'-map (evalSub (embWk w))                   ≈⟨ ✦'-map-pres-≈̇ (evalSub-pres-wk w) ⟩
    evalWk (keep🔒 w)                            ∎

abstract
  evalSub-pres-id : ∀ (Γ : Ctx) → evalSub idₛ[ Γ ] ≈̇ id'
  evalSub-pres-id Γ = let open EqReasoning (Sub'-setoid Γ Γ) in begin
    evalSub idₛ[ Γ ]  ≈⟨ evalSub-pres-wk idWk[ Γ ] ⟩
    evalWk idWk[ Γ ]  ≈⟨ evalWk-pres-id Γ ⟩
    id'                ∎

module _ {a : Ty} {Δ : Ctx} where
  abstract
    evalTm-pres-∘'' : ∀ (v : Var Γ a) (σ : Sub Δ Γ) → evalTm (substVar σ v) ≈̇ evalVar v [ evalSub σ ]'
    evalTm-pres-∘'' ze             (σ `, t) = ≈̇-sym (×'-beta-right (evalSub σ))
    evalTm-pres-∘'' (su {b = b} v) (σ `, t) = let open EqReasoning (Tm'-setoid Δ a) in begin
      evalTm (substVar (σ `, t) (su {b = b} v))       ≈⟨ evalTm-pres-∘'' v σ ⟩
      evalVar v [ evalSub σ ]'                        ≈˘⟨ ∘-pres-≈̇-right (evalVar v) (×'-beta-left (evalTm t)) ⟩
      evalVar v ∘ π₁'[ evalTy b ] ∘ evalSub (σ `, t)  ≈˘⟨ ∘-assoc (evalVar v) π₁'[ evalTy b ] (evalSub (σ `, t)) ⟩
      evalVar (su {b = b} v) [ evalSub (σ `, t) ]'    ∎

abstract
  evalTm-pres-∘ : ∀ (t : Tm Γ a) → (σ : Sub Δ Γ) → evalTm (substTm σ t) ≈̇ evalTm t [ evalSub σ ]'
  evalTm-pres-∘ (var v) σ = evalTm-pres-∘'' v σ
  evalTm-pres-∘ {a = a} {Δ} (lam {a = a'} t) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (lam t))
      ≈⟨ lam'-pres-≈̇ (evalTm-pres-∘ t (wkSub (fresh {Δ} {a'}) σ `, var ze)) ⟩
    lam' (evalTm t [ evalSub (wkSub (fresh {Δ} {a'}) σ `, var ze) ]')
      ≈⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (evalSub-pres-∘' σ (fresh {Δ} {a'})) π₂'[ evalCtx Δ ])) ⟩
    lam' (evalTm t [ ⟨ evalSub σ ∘ evalWk (fresh {Δ} {a'}) , π₂'[ evalCtx Δ ] ⟩' ]' )
      ≈⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (∘-pres-≈̇-right (evalSub σ) (evalWk-pres-π₁ Δ a')) π₂'[ evalCtx Δ ])) ⟩
    lam' (evalTm t [ ⟨ evalSub σ ∘ π₁'[ evalTy a' ] , π₂'[ evalCtx Δ ] ⟩' ]')
      ≈˘⟨ lam'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-right (evalSub σ ∘ π₁'[ evalTy a' ]) (id'-unit-left (evalTy a') π₂'[ evalCtx Δ ]))) ⟩
    lam' (evalTm t ∘ evalSub σ ×'-map id'[ evalTy a' ])
      ≈˘⟨ lam'-nat (evalTm t) (evalSub σ) ⟩
    evalTm (lam t) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (app t u) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (app t u))
      ≈⟨ app'-pres-≈̇ (evalTm-pres-∘ t σ) (evalTm-pres-∘ u σ) ⟩
    app' (evalTm t [ evalSub σ ]') (evalTm u [ evalSub σ ]')
      ≈˘⟨ app'-nat (evalTm t) (evalTm u) (evalSub σ) ⟩
    evalTm (app t u) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (box t) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (box t))
      ≈⟨ box'-pres-≈̇ (evalTm-pres-∘ t (lock σ new)) ⟩
    box' (evalTm t [ evalSub (keep🔒ₛ σ) ]')
      ≈⟨ box'-pres-≈̇ (∘-pres-≈̇-right (evalTm t) (evalSub-pres-lock-map σ)) ⟩
    box' (evalTm t [ ✦'-map (evalSub σ) ]')
      ≈⟨ box'-nat-dom (evalTm t) (evalSub σ) ⟩
    evalTm (box t) [ evalSub σ ]'
      ∎
  evalTm-pres-∘ {a = a} {Δ} (unbox t e) σ = let open EqReasoning (Tm'-setoid Δ a) in begin
    evalTm (substTm σ (unbox t e))
      ≈⟨ unbox'-pres-≈̇-left (evalTm-pres-∘ t (factor2Sub e σ)) (evalAcc (factor2Extₛ e σ)) ⟩
    unbox' (evalTm t [ evalSub (factor2Sub e σ) ]') (evalAcc (factor2Extₛ e σ))
      ≈⟨ unbox'-nat-dom (evalTm t) (evalSub (factor2Sub e σ)) (evalAcc (factor2Extₛ e σ)) ⟩
    unbox' (evalTm t) (✦'-map (evalSub (factor2Sub e σ)) ∘ evalAcc (factor2Extₛ e σ))
      ≈˘⟨ unbox'-pres-≈̇-right (evalTm t) (acc-nat e σ) ⟩
    unbox' (evalTm t) (evalAcc e ∘ evalSub σ)
      ≈˘⟨ ∘-assoc (λ' (evalTm t)) (evalAcc e) (evalSub σ) ⟩
    evalTm (unbox t e) [ evalSub σ ]'
      ∎

abstract
  evalTm-sound : (s : t ⟶ t') → evalTm t ≈̇ evalTm t'
  evalTm-sound (red-fun {Γ} {a} {b} t u) = let open EqReasoning (Tm'-setoid Γ b) in begin
    evalTm (app (lam t) u)
      ≈⟨ ⇒'-beta (evalTm t) (evalTm u) ⟩
    evalTm t [ ⟨ id'[ evalCtx Γ ] , evalTm u ⟩' ]'
      ≈˘⟨ ∘-pres-≈̇-right (evalTm t) (⟨,⟩'-pres-≈̇-left (evalSub-pres-id Γ) (evalTm u)) ⟩
    evalTm t [ ⟨ evalSub idₛ[ Γ ] , evalTm u ⟩' ]'
      ≈˘⟨ evalTm-pres-∘ t (idₛ `, u) ⟩
    evalTm (substTm (idₛ[ Γ ] `, u) t)
      ∎
  evalTm-sound (exp-fun {Γ} {a} {b} t) = let open EqReasoning (Tm'-setoid Γ (a ⇒ b)) in begin
    evalTm t
      ≈⟨ ⇒'-eta (evalTm t) ⟩
    lam' (app' (evalTm t [ π₁'[ evalTy a ] ]') π₂'[ evalCtx Γ ])
      ≈˘⟨ lam'-pres-≈̇ (app'-pres-≈̇-left (∘-pres-≈̇-right (evalTm t) (evalWk-pres-π₁ Γ a)) π₂'[ evalCtx Γ ]) ⟩
    lam' (app' (evalTm t [ evalWk (fresh {Γ} {a}) ]') π₂'[ evalCtx Γ ])
      ≈˘⟨ lam'-pres-≈̇ (app'-pres-≈̇-left (evalTm-pres-∘' fresh t) π₂'[ evalCtx Γ ]) ⟩
    evalTm (lam (app (wkTm fresh t) (var ze)))
      ∎
  evalTm-sound (red-box {ΓL} {a} {Γ} t e) = let open EqReasoning (Tm'-setoid Γ a) in begin
    evalTm (unbox (box t) e)
      ≈⟨ ∘-pres-≈̇-left (□'-beta (evalTm t)) (evalAcc e) ⟩
    evalTm t [ evalAcc e ]'
      ≈˘⟨ ∘-pres-≈̇-right (evalTm t) (id'-unit-left (✦' evalCtx ΓL) (evalAcc e)) ⟩
    evalTm t [ id'[ ✦' evalCtx ΓL ] ∘ evalAcc e ]'
      ≈˘⟨ ∘-pres-≈̇-right (evalTm t) (∘-pres-≈̇-left ✦'-map-pres-id' (evalAcc e)) ⟩
    evalTm t [ ✦'-map id'[ evalCtx ΓL ] ∘ evalAcc e ]'
      ≈˘⟨ ∘-pres-≈̇-right (evalTm t) (∘-pres-≈̇-left (✦'-map-pres-≈̇ (evalSub-pres-id ΓL)) (evalAcc e)) ⟩
    evalTm t [ evalSub (lock idₛ[ ΓL ] e)  ]'
      ≈˘⟨ evalTm-pres-∘ t (lock idₛ e) ⟩
    evalTm (substTm (lock idₛ[ ΓL ] e) t)
      ∎
  evalTm-sound (exp-box {Γ} {a} t) = let open EqReasoning (Tm'-setoid Γ (◻ a)) in begin
    evalTm t
      ≈⟨ □'-eta (evalTm t) ⟩
    box' (λ' (evalTm t))
      ≈˘⟨ box'-pres-≈̇ (id'-unit-right (✦' evalCtx Γ) (λ' (evalTm t))) ⟩
    box' (unbox' (evalTm t) id'[ ✦' evalCtx Γ ])
      ≈˘⟨ box'-pres-≈̇ (unbox'-pres-≈̇-right (evalTm t) η'-unit-right[ evalCtx Γ ]) ⟩
    evalTm (box (unbox t new))
      ∎
  evalTm-sound (cong-lam s)           = lam'-pres-≈̇        (evalTm-sound s)
  evalTm-sound (cong-app1 {u = u} s)  = app'-pres-≈̇-left   (evalTm-sound s) (evalTm u)
  evalTm-sound (cong-app2 {t = t} s)  = app'-pres-≈̇-right  (evalTm t) (evalTm-sound s)
  evalTm-sound (cong-box s)           = box'-pres-≈̇        (evalTm-sound s)
  evalTm-sound (cong-unbox {e = e} s) = unbox'-pres-≈̇-left (evalTm-sound s) (evalAcc e)

module _ {Γ : Ctx} {a : Ty} where
  abstract
    -- XXX: fold
    evalTm-sound' : ∀ {t t' : Tm Γ a} (t≈t' : t ≈ t') → evalTm t ≈̇ evalTm t'
    evalTm-sound' ε                     = ≈̇-refl
    evalTm-sound' (inj₁ t⟶t'' ◅ t''≈t') = ≈̇-trans (evalTm-sound t⟶t'') (evalTm-sound' t''≈t')
    evalTm-sound' (inj₂ t⟵t'' ◅ t''≈t') = ≈̇-trans (≈̇-sym (evalTm-sound t⟵t'')) (evalTm-sound' t''≈t')
