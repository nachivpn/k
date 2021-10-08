open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Semantics.Clouston.Evaluation.IML
  (Ctx' : Set₁)

  (_→̇_ : (P Q : Ctx') → Set) (let infixr 19 _→̇_; _→̇_ = _→̇_)

  (_≈̇_     : {P Q : Ctx'} → (φ ψ : P →̇ Q) → Set) (let infix 18 _≈̇_; _≈̇_ = _≈̇_)
  (≈̇-refl  : ∀ {P Q : Ctx'} {φ : P →̇ Q} → φ ≈̇ φ)
  (≈̇-sym   : ∀ {P Q : Ctx'} {φ ψ : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → ψ ≈̇ φ)
  (≈̇-trans : ∀ {P Q : Ctx'} {φ ψ ω : P →̇ Q} → (φ≈̇ψ : φ ≈̇ ψ) → (ψ≈̇ω : ψ ≈̇ ω) → φ ≈̇ ω)

  (_∘_       : {P Q R : Ctx'} → (ψ : Q →̇ R) → (φ : P →̇ Q) → (P →̇ R)) (let infixr 19 _∘_; _∘_ = _∘_)
  (∘-pres-≈̇ : ∀ {P Q R : Ctx'} {ψ ψ' : Q →̇ R} {φ φ' : P →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ' ∘ φ')
  (∘-assoc   : {P Q R S : Ctx'} → (ω : R →̇ S) → (ψ : Q →̇ R) → (φ : P →̇ Q) → (ω ∘ ψ) ∘ φ ≈̇ ω ∘ ψ ∘ φ)
  (let _[_]' = _∘_)

  (id'[_]         : (P : Ctx') → P →̇ P)
  (id'-unit-left  : ∀ {P : Ctx'} (Q : Ctx') (φ : P →̇ Q) → id'[ Q ] ∘ φ ≈̇ φ)
  (id'-unit-right : ∀ (P : Ctx') {Q : Ctx'} (φ : P →̇ Q) → φ ∘ id'[ P ] ≈̇ φ)

  ([]'     : Ctx')
  (unit'   : {P : Ctx'} → P →̇ []')
  ([]'-eta : ∀ {P : Ctx'} {φ : P →̇ []'} → φ ≈̇ unit')

  (_×'_          : (P Q : Ctx') → Ctx')
  (⟨_,_⟩'        : {R P Q : Ctx'} → (φ : R →̇ P) → (ψ : R →̇ Q) → R →̇ P ×' Q)
  (⟨,⟩'-pres-≈̇  : ∀ {R P Q : Ctx'} {φ φ' : R →̇ P} {ψ ψ' : R →̇ Q} (φ≈̇φ' : φ ≈̇ φ') (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ' ⟩')
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

  (_⇒'_ : (P Q : Ty') → Ty')

  (✦'_             : (P : Ctx') → Ctx')
  (✦'-map_         : {P Q : Ctx'} → (φ : P →̇ Q) → ✦' P →̇ ✦' Q)
  (✦'-map-pres-≈̇   : {P Q : Ctx'} {φ φ' : P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → ✦'-map φ ≈̇ ✦'-map φ')
  (✦'-map-pres-id' : {P : Ctx'} → ✦'-map id'[ P ] ≈̇ id'[ ✦' P ])

  (□'_  : (P : Ty') → Ty')
  where

open import Level using (0ℓ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import IK.Type

open import Context (Ty)

-- XXX: make parameters
private
  ≈̇-equiv : ∀ (P Q : Ctx') → IsEquivalence (_≈̇_ {P} {Q})
  ≈̇-equiv  P Q = record { refl = ≈̇-refl {P} {Q} ; sym = ≈̇-sym {P} {Q} ; trans = ≈̇-trans {P} {Q} }

  →̇-setoid : (P Q : Ctx') → Setoid 0ℓ 0ℓ
  →̇-setoid P Q = record { Carrier = P →̇ Q ; _≈_ = _≈̇_ ; isEquivalence = ≈̇-equiv P Q }

  ∘-pres-≈̇-left : ∀ {P Q R : Ctx'} {ψ ψ' : Q →̇ R} (ψ≈̇ψ' : ψ ≈̇ ψ') (φ : P →̇ Q) → ψ ∘ φ ≈̇ ψ' ∘ φ
  ∘-pres-≈̇-left ψ≈̇ψ' φ = ∘-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

  ∘-pres-≈̇-right : ∀ {P Q R : Ctx'} (ψ : Q →̇ R) {φ φ' : P →̇ Q} (φ≈̇φ' : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ ∘ φ'
  ∘-pres-≈̇-right ψ φ≈̇φ' = ∘-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

  id' = λ {P} → id'[ P ]

  π₁'       = λ {P} {Q} → π₁'[_] {P} Q
  π₁'[_][_] = λ P Q → π₁'[_] {P} Q

  π₂'       = λ {P} {Q} → π₂'[_] P {Q}
  π₂'[_][_] = λ P Q → π₂'[_] P {Q}

  abstract
    ⟨,⟩'-pres-≈̇-left : ∀ {R P Q : Ctx'} {φ φ' : R →̇ P} (φ≈̇φ' : φ ≈̇ φ') (ψ : R →̇ Q) → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ' , ψ ⟩'
    ⟨,⟩'-pres-≈̇-left ψ≈̇ψ' φ = ⟨,⟩'-pres-≈̇ ψ≈̇ψ' (≈̇-refl {φ = φ})

    ⟨,⟩'-pres-≈̇-right : ∀ {R P Q : Ctx'} (φ : R →̇ P) {ψ ψ' : R →̇ Q} (ψ≈̇ψ' : ψ ≈̇ ψ') → ⟨ φ , ψ ⟩' ≈̇ ⟨ φ , ψ' ⟩'
    ⟨,⟩'-pres-≈̇-right ψ φ≈̇φ' = ⟨,⟩'-pres-≈̇ (≈̇-refl {φ = ψ}) φ≈̇φ'

  -- Δ' : {P P : Ctx'} → P →̇ P ×' P

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

module Eval (N : Ty') where
  evalTy : (a : Ty) → Ty'
  evalTy 𝕓       = N
  evalTy (a ⇒ b) = evalTy a ⇒' evalTy b
  evalTy (◻ a)   = □' evalTy a

  evalCtx : (Γ : Ctx) → Ty'
  evalCtx []       = []'
  evalCtx (Γ `, a) = evalCtx Γ ×' evalTy a
  evalCtx (Γ 🔒)    = ✦' evalCtx Γ

  evalWk : (w : Γ ⊆ Δ) → evalCtx Δ →̇ evalCtx Γ
  evalWk base             = unit'
  evalWk (drop {a = a} w) = evalWk w ∘ π₁'[ evalTy a ]
  evalWk (keep {a = a} w) = evalWk w ×'-map id'[ evalTy a ]
  evalWk (keep🔒 w)        = ✦'-map (evalWk w)

  Sub' = λ Δ Γ → evalCtx Δ →̇ evalCtx Γ

  Sub'-setoid = λ Δ Γ → →̇-setoid (evalCtx Δ) (evalCtx Γ)

  Tm' = λ Γ a → evalCtx Γ →̇ evalTy a

  Tm'-setoid = λ Γ a → →̇-setoid (evalCtx Γ) (evalTy a)

  abstract
    evalWk-pres-id : ∀ (Γ : Ctx) → evalWk idWk[ Γ ] ≈̇ id'
    evalWk-pres-id [] = ≈̇-sym []'-eta
    evalWk-pres-id Γ@(Γ' `, a) = let open EqReasoning (Sub'-setoid Γ Γ) in begin
      evalWk (keep[ a ] idWk[ Γ' ])             ≈⟨ ×'-map-pres-≈̇-left (evalWk-pres-id Γ') id'[ evalTy a ] ⟩
      id'[ evalCtx Γ' ] ×'-map id'[ evalTy a ]  ≈⟨ ×'-map-pres-id' ⟩
      id'[ evalCtx Γ ]                          ∎
    evalWk-pres-id Γ@(Γ' 🔒) = let open EqReasoning (Sub'-setoid Γ Γ) in begin
      evalWk (keep🔒 idWk[ Γ' ])  ≈⟨ ✦'-map-pres-≈̇ (evalWk-pres-id Γ') ⟩
      ✦'-map id'[ evalCtx Γ' ]    ≈⟨ ✦'-map-pres-id' ⟩
      id'[ evalCtx Γ ]            ∎

    evalWk-pres-∘-π₁ : evalWk (drop[ a ] w) ≈̇ evalWk w ∘ π₁'[ evalTy a ]
    evalWk-pres-∘-π₁ = ≈̇-refl

    evalWk-pres-×-map-id : evalWk (keep[ a ] w) ≈̇ evalWk w ×'-map id'[ evalTy a ]
    evalWk-pres-×-map-id = ≈̇-refl

    evalWk-pres-π₁ : ∀ (Γ : Ctx) (a : Ty) → evalWk (fresh {Γ} {a}) ≈̇ π₁'[ evalTy a ]
    evalWk-pres-π₁ Γ a = let open EqReasoning (Sub'-setoid (Γ `, a) Γ) in begin
      evalWk (fresh {Γ} {a})              ≈⟨ ∘-pres-≈̇-left (evalWk-pres-id Γ) π₁'[ evalTy a ] ⟩
      id'[ evalCtx Γ ] ∘ π₁'[ evalTy a ]  ≈⟨ id'-unit-left (evalCtx Γ) π₁'[ evalTy a ] ⟩
      π₁'[ evalTy a ]                     ∎

    evalWk-pres-✦-map : evalWk (keep🔒 w) ≈̇ ✦'-map (evalWk w)
    evalWk-pres-✦-map = ≈̇-refl

  evalVar : (v : Var Γ a) → evalCtx Γ →̇ evalTy a
  evalVar (ze {Γ})       = π₂'[ evalCtx Γ ]
  evalVar (su {b = b} v) = evalVar v ∘ π₁'[ evalTy b ]

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
