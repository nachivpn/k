{-# OPTIONS --allow-unsolved-meta #-}

open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

module Semantics.Presheaf.CartesianClosure
  (C             : Set)
  (_⊆_           : (Γ Γ' : C) → Set)
  (⊆-refl        : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-trans       : ∀ {Γ Γ' Γ'' : C} → (w : Γ ⊆ Γ') → (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans w (⊆-trans w' w'') ≡ ⊆-trans (⊆-trans w w') w'')
  where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (_×_ to _∧_)

open import Semantics.Presheaf.Base C _⊆_

private
  variable
    Γ Δ Θ    : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh
    ℛ ℛ'     : Psh
    s s'     : 𝒫 →̇ 𝒬
    t t'     : 𝒫 →̇ 𝒬
    u u'     : 𝒫 →̇ 𝒬

Unit' : Psh
Unit' = record
  { Fam       = λ _ → ⊤
  ; _≋_       = λ _ _ → ⊤
  ; ≋-equiv   = {!!}
  ; wk        = λ _ _ → tt
  ; wk-pres-≋ = {!!}
  }

[]' = Unit'

unit' : ℛ →̇ Unit'
unit' = {!!}

Unit'-eta : t ≈̇ unit'
Unit'-eta = {!!}

[]'-eta = Unit'-eta

module _ (𝒫 𝒬 : Psh) where
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  record Fam (Γ : C) : Set where
    constructor elem
    field
      elem : P Γ × Q Γ

  private
    record _≋_ {Γ : C} (x y : Fam Γ) : Set where
      constructor proof
      field
        proof : let elem (p , q) = x; elem (p' , q') = y in p ≋[ 𝒫 ] p' ∧ q ≋[ 𝒬 ] q'

  _×'_ : Psh
  _×'_ = record
    { Fam       = Fam
    ; _≋_       = _≋_
    ; ≋-equiv   = {!!}
    ; wk        = λ w x → let elem (p , q) = x in elem (wk[ 𝒫 ] w p , wk[ 𝒬 ] w q)
    ; wk-pres-≋ = {!!}
    }

module _ {𝒫 𝒬 : Psh} where
  private instance _ = 𝒫; _ = 𝒬
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  π₁' : 𝒫 ×' 𝒬 →̇ 𝒫
  π₁' = {!!}

  π₂' : 𝒫 ×' 𝒬 →̇ 𝒬
  π₂' = {!!}

  fst' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒫
  fst' = π₁' ∘_

  snd' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒬
  snd' = π₂' ∘_

  pr' : (t : ℛ →̇ 𝒫) → (u : ℛ →̇ 𝒬) → ℛ →̇ 𝒫 ×' 𝒬
  pr' = {!!}

  ⟨_,_⟩' = pr'

  abstract
    pr'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → pr' t u ≈̇ pr' t' u'
    pr'-pres-≈̇ = {!!}

    ⟨,⟩'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → ⟨ t , u ⟩' ≈̇ ⟨ t' , u' ⟩'
    ⟨,⟩'-pres-≈̇ = pr'-pres-≈̇

    pr'-pres-≈̇-left : t ≈̇ t' → pr' t u ≈̇ pr' t' u
    pr'-pres-≈̇-left {u = u} t≈̇t' = pr'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    pr'-pres-≈̇-right : u ≈̇ u' → pr' t u ≈̇ pr' t u'
    pr'-pres-≈̇-right {t = t} u≈̇u' = pr'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

    pr'-nat : ∀ (t : ℛ →̇ 𝒫) (u : ℛ →̇ 𝒬) (s : ℛ' →̇ ℛ) → pr' t u ∘ s ≈̇ pr' (t ∘ s) (u ∘ s)
    pr'-nat = {!!}

    ⟨,⟩'-nat : ∀ (t : ℛ →̇ 𝒫) (u : ℛ →̇ 𝒬) (s : ℛ' →̇ ℛ) → ⟨ t , u ⟩' ∘ s ≈̇ ⟨ t ∘ s , u ∘ s ⟩'
    ⟨,⟩'-nat = {!!}

    ×'-beta-left : ∀ {t : ℛ →̇ 𝒫} (u : ℛ →̇ 𝒬) → fst' (pr' t u) ≈̇ t
    ×'-beta-left = {!!}

    ×'-beta-right : ∀ (t : ℛ →̇ 𝒫) {u : ℛ →̇ 𝒬} → snd' (pr' t u) ≈̇ u
    ×'-beta-right = {!!}

    ×'-eta : t ≈̇ pr' (fst' t) (snd' t)
    ×'-eta = {!!}

π₁'[_] = λ {𝒫} 𝒬 → π₁' {𝒫} {𝒬}

π₁'[_][_] = λ 𝒫 𝒬 → π₁' {𝒫} {𝒬}

π₂'[_] = λ 𝒫 {𝒬} → π₂' {𝒫} {𝒬}

π₂'[_][_] = λ 𝒫 𝒬 → π₂' {𝒫} {𝒬}

_×'-map_ : (t : 𝒫 →̇ 𝒫') → (u : 𝒬 →̇ 𝒬') → 𝒫 ×' 𝒬 →̇ 𝒫' ×' 𝒬'
_×'-map_ {𝒫 = 𝒫} {𝒬 = 𝒬} t u = pr' (t ∘ π₁'[ 𝒬 ]) (u ∘ π₂'[ 𝒫 ])

abstract
  ×'-map-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → t ×'-map u ≈̇ t' ×'-map u'
  ×'-map-pres-≈̇ = {!!}

  ×'-map-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : 𝒬 →̇ 𝒬') → t ×'-map u ≈̇ t' ×'-map u
  ×'-map-pres-≈̇-left t≈̇t' u = {!!}

  ×'-map-pres-≈̇-right : ∀ (t : 𝒫 →̇ 𝒫') (_ : u ≈̇ u') → t ×'-map u ≈̇ t ×'-map u'
  ×'-map-pres-≈̇-right t u≈̇u' = {!!}

  ×'-map-pres-id : id'[ 𝒫 ] ×'-map id'[ 𝒬 ] ≈̇ id'[ 𝒫 ×' 𝒬 ]
  ×'-map-pres-id = {!!}

module _ (𝒫 𝒬 : Psh) where
  private instance _ = 𝒫; _ = 𝒬
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  _⇒'_ : Psh
  _⇒'_ = record
    { Fam       = λ Γ → Σ ({Γ' : C} → (w : Γ ⊆ Γ') → P Γ' → Q Γ') λ f → ∀ {Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (p : P Γ') → f (⊆-trans w w') (wk[ 𝒫 ] w' p) ≋[ 𝒬 ] wk[ 𝒬 ] w' (f w p)
    ; _≋_       = λ {Γ} x y → let (f , f-natural) = x ; (g , g-natural) = y in ∀ {Δ : C} (w : Γ ⊆ Δ) p → f w p ≋[ 𝒬 ] g w p
    ; wk        = λ w x → let (f , f-natural) = x in ( (λ w' p → f (⊆-trans w w') p)
                                                     , (λ w' w'' p → subst (λ hole → f hole (wk[ 𝒫 ] w'' p) ≋[ 𝒬 ] wk[ 𝒬 ] w'' (f (⊆-trans w w') p)) (≡-sym (⊆-trans-assoc w w' w'')) (f-natural (⊆-trans w w') w'' p)))
    ; ≋-equiv   = {!!}
    ; wk-pres-≋ = {!!}
    }

module _ {𝒫 𝒬 : Psh} where
  app' : (t : ℛ →̇ 𝒫 ⇒' 𝒬) → (u : ℛ →̇ 𝒫) → ℛ →̇ 𝒬
  app' t u = record
    { fun     = λ r → let (f , _f-natural) = t .apply r in f ⊆-refl (u .apply r)
    ; pres-≋  = {!!}
    ; natural = {!!}
    }

  abstract
    app'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → app' t u ≈̇ app' t' u'
    app'-pres-≈̇ = {!!}

    app'-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : ℛ →̇ 𝒫) → app' t u ≈̇ app' t' u
    app'-pres-≈̇-left t≈̇t' u = app'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    app'-pres-≈̇-right : ∀ (t : ℛ →̇ 𝒫 ⇒' 𝒬) (_ : u ≈̇ u') → app' t u ≈̇ app' t u'
    app'-pres-≈̇-right t u≈̇u' = app'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

    app'-nat : ∀ (t : ℛ →̇ 𝒫 ⇒' 𝒬) (u : ℛ →̇ 𝒫) (s : ℛ' →̇ ℛ) → app' t u ∘ s ≈̇ app' (t ∘ s) (u ∘ s)
    app'-nat = {!!}

lam' : (t : ℛ ×' 𝒫 →̇ 𝒬) → ℛ →̇ 𝒫 ⇒' 𝒬
lam' {ℛ} t = record
  { fun     = λ r → (λ w x → t .apply (elem (wk[ ℛ ] w r , x))) , {!!}
  ; pres-≋  = {!!}
  ; natural = {!!} }

abstract
    lam'-pres-≈̇ : t ≈̇ t' → lam' t ≈̇ lam' t'
    lam'-pres-≈̇ = {!!}

    lam'-nat : ∀ (t : ℛ ×' 𝒫 →̇ 𝒬) (s : ℛ' →̇ ℛ) → lam' t ∘ s ≈̇ lam' (t ∘ s ×'-map id'[ 𝒫 ])
    lam'-nat = {!!}

    ⇒'-beta : ∀ (t : ℛ ×' 𝒫 →̇ 𝒬) (u : ℛ →̇ 𝒫) → app' (lam' t) u ≈̇ t [ pr' id' u ]'
    ⇒'-beta = {!!}

    ⇒'-eta : ∀ (t : ℛ →̇ 𝒫 ⇒' 𝒬) → t ≈̇ lam' {𝒬 = 𝒬} (app' (t [ π₁'[ 𝒫 ] ]') π₂'[ ℛ ])
    ⇒'-eta = {!!}
