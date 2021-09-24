open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; dcong)

module Semantics.Presheaf.Necessity
  (C               : Set)
  (_⊆_             : (Γ Δ : C) → Set)
  (⊆-refl          : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-trans         : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (_R_             : (Γ Δ : C) → Set)
  (factor1         : ∀ {Γ Γ' Δ' : C} → (w : Γ ⊆ Γ') → (r : Γ' R Δ') → ∃ λ Δ → Γ R Δ ∧ Δ ⊆ Δ')
  (let factor1C    : {Γ Γ' Δ' : C} → (w : Γ ⊆ Γ') → (r : Γ' R Δ') → C    ; factor1C = λ w r → factor1 w r .fst)
  (let factor1R    : ∀ {Γ Γ' Δ' : C} (w : Γ ⊆ Γ') (r : Γ' R Δ') → Γ R _  ; factor1R = λ w r → factor1 w r .snd .fst)
  (let factor1⊆    : ∀ {Γ Γ' Δ' : C} (w : Γ ⊆ Γ') (r : Γ' R Δ') → _ ⊆ Δ' ; factor1⊆ = λ w r → factor1 w r .snd .snd)
  (factor2         : ∀ {Γ Δ Δ' : C} → (r : Γ R Δ) → (w : Δ ⊆ Δ') → ∃ λ Γ' → Γ ⊆ Γ' ∧ Γ' R Δ')
  (let factor2C    : {Γ Δ Δ' : C} → (r : Γ R Δ) → (w : Δ ⊆ Δ') → C    ; factor2C = λ r w → factor2 r w .fst)
  (let factor2⊆    : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → Γ ⊆ _  ; factor2⊆ = λ r w → factor2 r w .snd .fst)
  (let factor2R    : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → _ R Δ' ; factor2R = λ r w → factor2 r w .snd .snd)
  (factor2-factor1 : ∀ {Γ Γ' Δ' : C} → (w : Γ ⊆ Γ') → (r : Γ' R Δ') → factor2 (factor1R w r) (factor1⊆ w r) ≡ (-, w , r))
  (factor1-factor2 : ∀ {Γ Δ  Δ' : C} → (r : Γ R Δ)  → (w : Δ ⊆ Δ')  → factor1 (factor2⊆ r w) (factor2R r w) ≡ (-, r , w))
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_

private
  variable
    Γ Γ'     : C
    Δ Δ'     : C
    Θ Θ'     : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh
    ℛ ℛ' ℛ'' : Psh
    s s'     : 𝒫 →̇ 𝒬
    t t'     : 𝒫 →̇ 𝒬
    u u'     : 𝒫 →̇ 𝒬

-- XXX: ✦ 𝒫 and □ 𝒫 can be expressed internally as the dependent sum
-- and product over the types R⁻¹ and R, respectively. This should
-- reduce the constructions to showing that R⁻¹ and R are types (and
-- thereby simplify them), which is implied by the two frame
-- conditions.

record ✦'-Fam (𝒫 : Psh) (Γ : C) : Set where
  constructor elem
  field
    elem : Σ λ Δ → Δ R Γ × 𝒫 ₀ Δ

private
  record _✦'-≋_ {𝒫 : Psh} {Γ : C} (x x' : ✦'-Fam 𝒫 Γ) : Set where
    constructor proof
    field
      proof : let elem (Δ , r , p) = x; elem (Δ' , r' , p') = x' in ∃ λ Δ≡Δ' → subst (_R _) Δ≡Δ' r ≡ r' ∧ subst (𝒫 ₀_) Δ≡Δ' p ≋[ 𝒫 ] p'

✦'_ : (𝒫 : Psh) → Psh -- type \blacklozenge
✦' 𝒫 = record
  { Fam       = ✦'-Fam 𝒫
  ; _≋_       = _✦'-≋_
  ; ≋-equiv   = ≋-equiv
  ; wk        = wk
  ; wk-pres-≋ = wk-pres-≋
  }
  where
    abstract
      ≋-equiv : (Γ : C) → IsEquivalence (_✦'-≋_ {𝒫} {Γ})
      ≋-equiv = λ Γ → record
        { refl  = proof (refl , refl , ≋-refl[ 𝒫 ])
        ; sym   = λ { (proof (refl , r≡r' , p≋p')) → proof (refl , sym r≡r' , ≋-sym[ 𝒫 ] p≋p') }
        ; trans = λ { (proof (refl , r≡r' , p≋p')) (proof (refl , r'≡r'' , p'≋p'')) → proof (refl , trans r≡r' r'≡r'' , ≋-trans[ 𝒫 ] p≋p' p'≋p'') }
        }

    wk : (w : Γ ⊆ Γ') → (x : ✦'-Fam 𝒫 Γ) → ✦'-Fam 𝒫 Γ'
    wk = λ w x → let elem (Δ , r , p) = x; (Δ' , w' , r') = factor2 r w in elem (Δ' , r' , wk[ 𝒫 ] w' p)

    abstract
      wk-pres-≋ : ∀ (w : Γ ⊆ Γ') {x x' : ✦'-Fam 𝒫 Γ} (x≋x' : x ✦'-≋ x') → wk w x ✦'-≋ wk w x'
      wk-pres-≋ w (proof (refl , refl , p≋p')) = proof (refl , refl , wk-pres-≋[ 𝒫 ] _ p≋p')

abstract
  ✦'-map_ : (t : 𝒫 →̇ 𝒬) → ✦' 𝒫 →̇ ✦' 𝒬
  ✦'-map_ {_} {𝒬} t = record
    { fun     = λ x → let elem (Δ , r , p) = x in elem (Δ , r , t .apply p)
    ; pres-≋  = λ { (proof (refl , r≡r' , p≋p')) → proof (refl , r≡r' , t .apply-≋ p≋p') }
    ; natural = λ w x → let elem (Δ , r , p) = x in proof (refl , refl , t .natural _ p)
    }

  ✦'-map-pres-≈̇ : t ≈̇ t' → ✦'-map t ≈̇ ✦'-map t'
  ✦'-map-pres-≈̇ t≈̇t' = record { proof = λ x → let elem (_ , _ , p) = x in proof (refl , refl , t≈̇t' .apply-≋ p) }

  ✦'-map-pres-id' : ✦'-map id'[ 𝒫 ] ≈̇ id'
  ✦'-map-pres-id' {𝒫} = record { proof = λ p → proof (refl , refl , ≋-refl[ 𝒫 ]) }

  ✦'-map-pres-∘ : ∀ (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ✦'-map (t' ∘ t) ≈̇ ✦'-map t' ∘ ✦'-map t
  ✦'-map-pres-∘ {ℛ = ℛ} _ _ = record { proof = λ p → proof (refl , refl , ≋-refl[ ℛ ]) }

module IS4
  (R-trans            : ∀ {Γ Δ Θ : C} (r : Γ R Δ) (r' : Δ R Θ) → Γ R Θ)
  (R-trans-assoc      : ∀ {Γ Δ Θ Ξ : C} (r : Γ R Δ) (r' : Δ R Θ) (r'' : Θ R Ξ) → R-trans r (R-trans r' r'') ≡ R-trans (R-trans r r') r'')
  (R-refl             : ∀ {Γ : C} → Γ R Γ)
  (R-refl-unit-left   : ∀ {Γ Δ : C} (r : Γ R Δ) → R-trans r R-refl ≡ r)
  (R-refl-unit-right  : ∀ {Γ Δ : C} (r : Γ R Δ) → R-trans R-refl r ≡ r)
  (let factor2C       : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → C      ; factor2C r w = factor2 r w .fst)
  (let factor2⊆       : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → Γ ⊆ _  ; factor2⊆ r w = factor2 r w .snd .fst)
  (let factor2R       : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → _ R Δ' ; factor2R r w = factor2 r w .snd .snd)
  (factor2-pres-refl  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → factor2 R-refl w ≡ (Γ' , w , R-refl))
  (factor2-pres-trans : ∀ {Γ Δ Θ Θ' : C} (r : Γ R Δ) (r' : Δ R Θ) (w : Θ ⊆ Θ') → factor2 (R-trans r r') w ≡ (factor2C r (factor2⊆ r' w) , factor2⊆ r _ , R-trans (factor2R r _) (factor2R r' w)))
  where
    η'[_] : (𝒫 : Psh) → 𝒫 →̇ ✦' 𝒫
    η'[_] 𝒫 = record
      { fun     = λ {Γ} p → elem (Γ , R-refl , p)
      ; pres-≋  = λ p≋p' → proof (refl , refl , p≋p')
      ; natural = λ w p → let open EqReasoning ≋[ ✦' 𝒫 ]-setoid in begin
          elem (-, factor2R R-refl w , wk[ 𝒫 ] (factor2⊆ R-refl w) p)
            ≡⟨ cong (λ { (_ , w , r) → elem (-, r , wk[ 𝒫 ] w p) }) (factor2-pres-refl w) ⟩
          elem (-, R-refl , wk[ 𝒫 ] w p)
            ∎
      }

    abstract
      η'-nat : ∀ (φ : 𝒫 →̇ 𝒬) → ✦'-map φ ∘ η'[ 𝒫 ] ≈̇ η'[ 𝒬 ] ∘ φ
      η'-nat {_} {𝒬} φ = record { proof = λ p → proof (refl , refl , ≋-refl[ 𝒬 ]) }

    μ'[_] : (𝒫 : Psh) → ✦' ✦' 𝒫 →̇ ✦' 𝒫
    μ'[_] 𝒫 = record
      { fun     = λ x → let elem (Δ , r' , elem (Γ , r , p)) = x in elem (Γ , R-trans r r' , p)
      ; pres-≋  = λ { (proof (refl , refl , proof (refl , refl , p≋p'))) → proof (refl , refl , p≋p') }
      ; natural = λ w x → let elem (Δ , r' , elem (Γ , r , p)) = x; open EqReasoning ≋[ ✦' 𝒫 ]-setoid in begin
          elem (-, factor2R (R-trans r r') w , wk[ 𝒫 ] (factor2⊆ (R-trans r r') w) p)
            ≡⟨ cong (λ { (_ , w , r) → elem (-, r , wk[ 𝒫 ] w p) }) (factor2-pres-trans r r' w) ⟩
          elem (-, R-trans (factor2R r (factor2⊆ r' w)) (factor2R r' w) , wk[ 𝒫 ] (factor2⊆ r (factor2⊆ r' w)) p)
            ∎
      }

    abstract
      μ'-nat : ∀ (φ : 𝒫 →̇ 𝒬) → ✦'-map φ ∘ μ'[ 𝒫 ] ≈̇ μ'[ 𝒬 ] ∘ ✦'-map ✦'-map φ
      μ'-nat {_} {𝒬} φ = record { proof = λ p → proof (refl , refl , ≋-refl[ 𝒬 ]) }

      η'-unit-left[_] : ∀ (𝒫 : Psh) → μ'[ 𝒫 ] ∘ η'[ ✦' 𝒫 ] ≈̇ id'[ ✦' 𝒫 ]
      η'-unit-left[_] 𝒫 = record { proof = λ x → let elem (_ , r , p) = x in proof (refl , R-refl-unit-left r , ≋-refl[ 𝒫 ]) }

      η'-unit-right[_] : ∀ (𝒫 : Psh) → μ'[ 𝒫 ] ∘ ✦'-map η'[ 𝒫 ] ≈̇ id'[ ✦' 𝒫 ]
      η'-unit-right[_] 𝒫 = record { proof = λ x → let elem (_ , r , p) = x in proof (refl , R-refl-unit-right r , ≋-refl[ 𝒫 ]) }

      μ'-assoc[_] : ∀ (𝒫 : Psh) → μ'[ 𝒫 ] ∘ μ'[ ✦' 𝒫 ] ≈̇ μ'[ 𝒫 ] ∘ ✦'-map μ'[ 𝒫 ]
      μ'-assoc[_] 𝒫 = record { proof = λ x → let elem (_ , r'' , elem (_ , r' , elem (_ , r , p))) = x in proof (refl , R-trans-assoc r r' r'' , ≋-refl[ 𝒫 ]) }

    η'            = λ {𝒫} → η'[ 𝒫 ]
    μ'            = λ {𝒫} → μ'[ 𝒫 ]
    η'-unit-left  = λ {𝒫} → η'-unit-left[ 𝒫 ]
    η'-unit-right = λ {𝒫} → η'-unit-right[ 𝒫 ]
    μ'-assoc      = λ {𝒫} → μ'-assoc[ 𝒫 ]

□'_ : (𝒫 : Psh) → Psh -- type \Box
□'_ 𝒫 = record
  { Fam       = Fam
  ; _≋_       = _≋_
  ; ≋-equiv   = ≋-equiv
  ; wk        = wk
  ; wk-pres-≋ = wk-pres-≋
  }
  where
    Fam : (Γ : C) → Set
    Fam = λ Γ → {Δ : C} → (r : Γ R Δ) → 𝒫 ₀ Δ

    _≋_ : {Γ : C} → (x x' : Fam Γ) → Set
    _≋_ {Γ} = λ x y → ∀ {Δ : C} {r r' : Γ R Δ} (r≡r' : r ≡ r') → x r ≋[ 𝒫 ] y r'

    abstract
      ≋-equiv : (Γ : C) → IsEquivalence (_≋_ {Γ})
      ≋-equiv = λ Γ → record
        { refl  = λ r≡r'             → ≋-reflexive[ 𝒫 ] (cong _ r≡r')
        ; sym   = λ x≋x' r≡r'        → ≋-sym[ 𝒫 ] (x≋x' (sym r≡r'))
        ; trans = λ x≋x' x'≋x'' r≡r' → ≋-trans[ 𝒫 ] (x≋x' r≡r') (x'≋x'' refl)
        }

    wk : (w : Γ ⊆ Γ') → (x : Fam Γ) → Fam Γ'
    wk = λ w x → λ r → let (Δ , r' , w') = factor1 w r in wk[ 𝒫 ] w' (x r')

    abstract
      wk-pres-≋ : ∀ (w : Γ ⊆ Γ') {x x' : Fam Γ} (x≋x' : x ≋ x') → wk w x ≋ wk w x'
      wk-pres-≋ w x≋x' {r = r} {r} refl = wk-pres-≋[ 𝒫 ] (factor1⊆ w r) (x≋x' refl)

abstract
  □'-map_ : (t : 𝒫 →̇ 𝒬) → □' 𝒫 →̇ □' 𝒬
  □'-map_ t = record
    { fun     = λ p r → t .apply (p r)
    ; pres-≋  = λ p≋p' r≡r' → t .apply-≋ (p≋p' r≡r')
    ; natural = λ { w p {r = r} {.r} refl → t .natural (factor1⊆ w r) (p (factor1R w r)) }
    }

box' : (t : ✦' 𝒫 →̇ 𝒬) → 𝒫 →̇ □' 𝒬
box' {𝒫} {𝒬} t = record
  { fun     = λ p r → t .apply (elem (_ , r , p))
  ; pres-≋  = λ p≋p' r≡r'  → t .apply-≋ (proof (refl , r≡r' , p≋p'))
  ; natural = λ { w p {r = r} {r'} r≡r' → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
      wk[ 𝒬 ] (factor1⊆ w r) (t .apply (elem (-, factor1R w r , p)))
        ≈⟨ t .natural (factor1⊆ w r) (elem (-, factor1R w r , p)) ⟩
      t .apply (elem (-, factor2R (factor1R w r) (factor1⊆ w r) , wk[ 𝒫 ] (factor2⊆ (factor1R w r) (factor1⊆ w r)) p))
        ≡⟨ cong (λ { (_ , w , r) → t .apply (elem (-, r , wk[ 𝒫 ] w p)) }) (factor2-factor1 w r) ⟩
      t .apply (elem (-, r , wk[ 𝒫 ] w p))
        ≡⟨ cong (λ r → t .apply (elem (-, r , wk[ 𝒫 ] w p))) r≡r' ⟩
      t .apply (elem (-, r' , wk[ 𝒫 ] w p))
        ∎
      }
  }

abstract
  box'-pres-≈̇ : t ≈̇ t' → box' t ≈̇ box' t'
  box'-pres-≈̇ t≈̇t' = record { proof = λ { p refl → t≈̇t' .apply-≋ (elem (_ , _ , p)) } }

λ' : (t : 𝒫 →̇ □' 𝒬) → ✦' 𝒫 →̇ 𝒬
λ' {𝒫} {𝒬} t = record
  { fun     = λ x → let elem (_ , r , p) = x in t .apply p r
  ; pres-≋  = λ { (proof (refl , r≡r' , p≋p')) → t .apply-≋ p≋p' r≡r' }
  ; natural = λ w x → let elem (_ , r , p) = x; open EqReasoning ≋[ 𝒬 ]-setoid in begin
      wk[ 𝒬 ] w (t .apply p r)
        ≡˘⟨ cong (λ { (_ , r , w) → wk[ 𝒬 ] w (t .apply p r) }) (factor1-factor2 r w) ⟩
      wk[ 𝒬 ] (factor1⊆ (factor2⊆ r w) (factor2R r w)) (t .apply p (factor1R (factor2⊆ r w) (factor2R r w)))
        ≈⟨ t .natural (factor2⊆ r w) p refl ⟩
      t .apply (wk[ 𝒫 ] (factor2⊆ r w) p) (factor2R r w)
        ∎
  }

abstract
  λ'-pres-≈̇ : t ≈̇ t' → λ' t ≈̇ λ' t'
  λ'-pres-≈̇ t≈̇t' = record { proof = λ x → let elem (_ , r , p) = x in t≈̇t' .apply-≋ p refl }

unbox' : (t : 𝒫 →̇ □' 𝒬) → (s : ℛ →̇ ✦' 𝒫) → ℛ →̇ 𝒬
unbox' t s = λ' t ∘ s

abstract
  unbox'-pres-≈̇ : t ≈̇ t' → s ≈̇ s' → unbox' t s ≈̇ unbox' t' s'
  unbox'-pres-≈̇ t≈̇t' s≈̇s' = ∘-pres-≈̇ (λ'-pres-≈̇ t≈̇t') s≈̇s'

  unbox'-pres-≈̇-left : ∀ {t t' : 𝒫 →̇ □' 𝒬} (t≈̇t' : t ≈̇ t') (s : ℛ →̇ ✦' 𝒫) → unbox' t s ≈̇ unbox' t' s
  unbox'-pres-≈̇-left t≈̇t' s = unbox'-pres-≈̇ t≈̇t' (≈̇-refl {x = s})

  unbox'-pres-≈̇-right : s ≈̇ s' → unbox' t s ≈̇ unbox' t s'
  unbox'-pres-≈̇-right {t = t} s≈̇s' = unbox'-pres-≈̇ (≈̇-refl {x = t}) s≈̇s'

  □'-beta : ∀ (t : ✦' 𝒫 →̇ 𝒬) → λ' (box' t) ≈̇ t
  □'-beta {_} {𝒬} _t = record { proof = λ _p → ≋-refl[ 𝒬 ] }

  □'-eta : ∀ (t : 𝒫 →̇ □' 𝒬) → t ≈̇ box' (λ' t)
  □'-eta {_} {𝒬} _t = record { proof = λ { _p refl → ≋-refl[ 𝒬 ] } }

  box'-nat-dom : ∀ (t : ✦' 𝒫 →̇ 𝒬) (t' : 𝒫' →̇ 𝒫) → box' (t ∘ ✦'-map t') ≈̇ box' t ∘ t'
  box'-nat-dom {𝒬 = 𝒬} _t _t' = record { proof = λ { _p' refl → ≋-refl[ 𝒬 ] } }

  box'-nat-cod : ∀ (t' : 𝒬 →̇ 𝒬') (t : ✦' 𝒫 →̇ 𝒬) → box' (t' ∘ t) ≈̇ □'-map t' ∘ box' t
  box'-nat-cod {𝒬' = 𝒬'} _t' _t = record { proof = λ { _p refl → ≋-refl[ 𝒬' ] } }

  λ'-nat-dom : ∀ (t : 𝒫 →̇ □' 𝒬) (t' : 𝒫' →̇ 𝒫) → λ' (t ∘ t') ≈̇ λ' t ∘ ✦'-map t'
  λ'-nat-dom {𝒬 = 𝒬} _t _t' = record { proof = λ x → let elem (_Δ , _r , _p') = x in ≋-refl[ 𝒬 ] }

  λ'-nat-cod : ∀ (t' : 𝒬 →̇ 𝒬') (t : 𝒫 →̇ □' 𝒬) → λ' (□'-map t' ∘ t) ≈̇ t' ∘ λ' t
  λ'-nat-cod {𝒬' = 𝒬'} _t' _t = record { proof = λ x → let elem (_Δ , _r , _p) = x in ≋-refl[ 𝒬' ] }

  unbox'-nat-dom : ∀ (t : 𝒫 →̇ □' 𝒬) (t' : 𝒫' →̇ 𝒫) (s : ℛ →̇ ✦' 𝒫') → unbox' (t ∘ t') s ≈̇ unbox' t (✦'-map t' ∘ s)
  unbox'-nat-dom {𝒫} {𝒬} {𝒫'} {ℛ} t t' s = let open EqReasoning (→̇-setoid ℛ 𝒬) in begin
    unbox' (t ∘ t') s       ≡⟨⟩
    λ' (t ∘ t')        ∘ s  ≈⟨ ∘-pres-≈̇-left (λ'-nat-dom t t') s ⟩
    (λ' t ∘ ✦'-map t') ∘ s  ≈⟨ ∘-assoc (λ' t) (✦'-map t') s ⟩
    λ' t ∘ ✦'-map t' ∘ s    ∎

  unbox'-nat-cod : ∀ (t' : 𝒬 →̇ 𝒬') (t : 𝒫 →̇ □' 𝒬) (s : ℛ →̇ ✦' 𝒫) → unbox' (□'-map t' ∘ t) s ≈̇ t' ∘ unbox' t s
  unbox'-nat-cod {𝒬} {𝒬'} {𝒫} {ℛ} t' t s = let open EqReasoning (→̇-setoid ℛ 𝒬') in begin
    unbox' (□'-map t' ∘ t) s  ≡⟨⟩
    λ' (□'-map t' ∘ t) ∘ s    ≈⟨ ∘-pres-≈̇-left (λ'-nat-cod t' t) s ⟩
    (t' ∘ λ' t)        ∘ s    ≈⟨ ∘-assoc t' (λ' t) s ⟩
    t' ∘ unbox' t s           ∎
