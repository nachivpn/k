{-# OPTIONS --safe --without-K #-}
module Semantics.Presheaf.Base
  (C       : Set)
  (_⊆_     : (Γ Γ' : C) → Set)
  (⊆-refl  : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-trans : ∀ {Γ Γ' Γ'' : C} → (_w : Γ ⊆ Γ') → (_w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  where

open import Level using (0ℓ)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

infixr 19 _∘_
infix  18 _→̇_ _≈̇_

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    Θ Θ' Θ'' : C
    w w' w'' : Γ ⊆ Δ

record Psh : Set₁ where
  no-eta-equality
  field
    -- setoids
    Fam       : (Γ : C) → Set
    _≋_       : (x y : Fam Γ) → Set -- type \~~~
    ≋-equiv   : ∀ (Γ : C) → IsEquivalence {A = Fam Γ} _≋_

    -- setoid morphisms
    wk        : (w : Γ ⊆ Δ) → (x : Fam Γ) → Fam Δ
    wk-pres-≋ : ∀ (w : Γ ⊆ Δ) {x y : Fam Γ} (x≋y : x ≋ y) → wk w x ≋ wk w y

    -- functoriality
    wk-pres-refl  : ∀ (x : Fam Γ) → wk ⊆-refl x ≋ x
    wk-pres-trans : ∀ (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (x : Fam Γ) → wk (⊆-trans w w') x ≋ wk w' (wk w x)

  infix 19 Fam

  Fam-setoid : {Γ : C} → Setoid _ _
  Fam-setoid {Γ} = record
    { Carrier       = Fam Γ
    ; _≈_           = _≋_
    ; isEquivalence = ≋-equiv Γ
    }

  wk-pres-≡-≋ : ∀ {w w' : Γ ⊆ Δ} (w≡w' : w ≡ w') {x y : Fam Γ} (x≋y : x ≋ y) → wk w x ≋ wk w' y
  wk-pres-≡-≋ {w = w} {.w} refl = wk-pres-≋ w

  module _ {Γ : C} where
    open IsEquivalence (≋-equiv Γ) public
      using ()
      renaming
        ( refl      to ≋-refl
        ; sym       to ≋-sym
        ; trans     to ≋-trans
        ; reflexive to ≋-reflexive
        )

  ≋-reflexive˘ : ∀ {x y : Fam Γ} → y ≡ x → x ≋ y
  ≋-reflexive˘ refl = ≋-refl

-- open Psh {{...}} using (_≋_; ≋-refl; ≋-sym; ≋-trans; wk) public
-- ≋-refl  = λ {𝒫} {Γ} {p}         → 𝒫 .Psh.≋-refl {Γ} {p}
-- ≋-sym   = λ {𝒫} {Γ} {p} {q}     → 𝒫 .Psh.≋-sym {Γ} {p} {q}
-- ≋-trans = λ {𝒫} {Γ} {p} {q} {r} → 𝒫 .Psh.≋-trans {Γ} {p} {q} {r}
open Psh public
  using ()
  renaming
    ( Fam           to _₀_
    ; Fam-setoid    to ≋[_]-setoid
    ; ≋-refl        to ≋[_]-refl
    ; ≋-sym         to ≋[_]-sym
    ; ≋-trans       to ≋[_]-trans
    ; ≋-reflexive   to ≋[_]-reflexive
    ; ≋-reflexive˘   to ≋[_]-reflexive˘
    ; wk            to wk[_]
    ; wk-pres-≋     to wk[_]-pres-≋
    ; wk-pres-refl  to wk[_]-pres-refl
    ; wk-pres-trans to wk[_]-pres-trans
    )

private
  variable
    𝒫 𝒫' : Psh -- type \McP
    𝒬 𝒬' : Psh -- type \McQ
    ℛ ℛ' : Psh -- type \McR
    𝒮 𝒮' : Psh -- type \McS

≋[]-syntax : (𝒫 : Psh) → (x y : 𝒫 ₀ Γ) → Set
≋[]-syntax 𝒫 = 𝒫 .Psh._≋_

syntax ≋[]-syntax 𝒫 x y = x ≋[ 𝒫 ] y

record _→̇_ (𝒫 𝒬 : Psh) : Set where -- type \-> \^.
  no-eta-equality
  field
    fun     : (p : 𝒫 ₀ Γ) → 𝒬 ₀ Γ
    pres-≋  : ∀ {p p' : 𝒫 ₀ Γ} (p≋p' : p ≋[ 𝒫 ] p') → fun p ≋[ 𝒬 ] fun p'
    natural : ∀ (w : Γ ⊆ Δ) (p : 𝒫 ₀ Γ) → wk[ 𝒬 ] w (fun p) ≋[ 𝒬 ] fun (wk[ 𝒫 ] w p)

open _→̇_ using (natural) renaming (fun to apply; pres-≋ to apply-≋) public

record _≈̇_ (φ ψ : 𝒫 →̇ 𝒬) : Set where -- type \~~ \^.
  no-eta-equality
  field
    proof : ∀ (p : 𝒫 ₀ Γ) → φ .apply p ≋[ 𝒬 ] ψ .apply p

  apply-sq : ∀ {p p' : 𝒫 ₀ Γ} → p ≋[ 𝒫 ] p' → φ .apply p ≋[ 𝒬 ] ψ .apply p' -- XXX: rename
  apply-sq {p = p} {p'} p≋p' = let open EqReasoning ≋[ 𝒬 ]-setoid in begin
    φ .apply p   ≈⟨ φ .apply-≋ p≋p' ⟩
    φ .apply p'  ≈⟨ proof p' ⟩
    ψ .apply p'  ∎

open _≈̇_ using (apply-sq) renaming (proof to apply-≋) public

private
  variable
    φ φ' : 𝒫 →̇ 𝒬
    ψ ψ' : 𝒫 →̇ 𝒬
    ω ω' : 𝒫 →̇ 𝒬

module _ {𝒫 𝒬 : Psh} where
  abstract
    ≈̇-refl : Reflexive {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-refl = record { proof = λ {_} _ → ≋[ 𝒬 ]-refl }

    ≈̇-sym : Symmetric {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-sym φ≋φ' = record { proof = λ {_} p → ≋[ 𝒬 ]-sym (φ≋φ' ._≈̇_.proof p) }

    ≈̇-trans : Transitive {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-trans φ≋ψ ψ≋ω = record { proof = λ {_} p → ≋[ 𝒬 ]-trans (φ≋ψ ._≈̇_.proof p) (ψ≋ω ._≈̇_.proof p) }

    ≈̇-equiv : IsEquivalence {A = 𝒫 →̇ 𝒬} _≈̇_
    ≈̇-equiv = record
      { refl  = ≈̇-refl
      ; sym   = ≈̇-sym
      ; trans = ≈̇-trans
      }

module _ (𝒫 𝒬 : Psh) where
  →̇-setoid : Setoid 0ℓ 0ℓ
  →̇-setoid = record
    { Carrier       = 𝒫 →̇ 𝒬
    ; _≈_           = _≈̇_
    ; isEquivalence = ≈̇-equiv
    }

_∘_ : (ψ : 𝒬 →̇ ℛ) → (φ : 𝒫 →̇ 𝒬) → 𝒫 →̇ ℛ
_∘_ {𝒬} {ℛ} {𝒫} ψ φ = record
  { fun     = λ p → ψ .apply (φ .apply p)
  ; pres-≋  = λ p≋p' → ψ .apply-≋ (φ .apply-≋ p≋p')
  ; natural = λ w p → let open EqReasoning ≋[ ℛ ]-setoid in begin
      wk[ ℛ ] w (ψ .apply (φ .apply p))  ≈⟨ ψ .natural _ _ ⟩
      ψ .apply (wk[ 𝒬 ] w (φ .apply p))  ≈⟨ ψ .apply-≋ (φ .natural _ _) ⟩
      ψ .apply (φ .apply (wk[ 𝒫 ] w p))  ∎
  }

_[_]' = _∘_

abstract
  ∘-pres-≈̇ : ψ ≈̇ ψ' → φ ≈̇ φ' → ψ ∘ φ ≈̇ ψ' ∘ φ'
  ∘-pres-≈̇ ψ≈̇ψ' φ≈̇φ' = record { proof = λ p → apply-sq ψ≈̇ψ' (φ≈̇φ' .apply-≋ p) }

  ∘-pres-≈̇-left : ∀ (_ : ψ ≈̇ ψ') (φ : 𝒫 →̇ 𝒬) → ψ ∘ φ ≈̇ ψ' ∘ φ
  ∘-pres-≈̇-left ψ≈̇ψ' φ = ∘-pres-≈̇ ψ≈̇ψ' (≈̇-refl {x = φ})

  ∘-pres-≈̇-right : ∀ (ψ : 𝒬 →̇ ℛ) (_ : φ ≈̇ φ') → ψ ∘ φ ≈̇ ψ ∘ φ'
  ∘-pres-≈̇-right ψ φ≈̇φ' = ∘-pres-≈̇ (≈̇-refl {x = ψ}) φ≈̇φ'

  ∘-assoc : ∀ (ω : ℛ →̇ 𝒮) (ψ : 𝒬 →̇ ℛ) (φ : 𝒫 →̇ 𝒬) → (ω ∘ ψ) ∘ φ ≈̇ ω ∘ ψ ∘ φ
  ∘-assoc {_} {ℛ} ω ψ φ = record { proof = λ p → ≋[ ℛ ]-refl }

id'[_] : (𝒫 : Psh) → 𝒫 →̇ 𝒫
id'[_] 𝒫 = record
  { fun     = λ p → p
  ; pres-≋  = λ p≋p' → p≋p'
  ; natural = λ _ _ → ≋[ 𝒫 ]-refl
  }

id' = λ {𝒫} → id'[ 𝒫 ]

abstract
  id'-unit-left : ∀ {𝒫 : Psh} (𝒬 : Psh) (φ : 𝒫 →̇ 𝒬) → id'[ 𝒬 ] ∘ φ ≈̇ φ
  id'-unit-left 𝒬 _ = record { proof = λ p → ≋[ 𝒬 ]-refl }

  id'-unit-right : ∀ (𝒫 : Psh) {𝒬 : Psh} (φ : 𝒫 →̇ 𝒬) → φ ∘ id'[ 𝒫 ] ≈̇ φ
  id'-unit-right _ {𝒬} _ = record { proof = λ p → ≋[ 𝒬 ]-refl }
