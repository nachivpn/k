{-# OPTIONS --safe --without-K #-}
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (∃ to Σ; _×_ to _∧_)

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

module Semantics.Presheaf.Necessity
  (C                 : Set)
  (_⊆_               : (Γ Δ : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans w (⊆-trans w' w'') ≡ ⊆-trans (⊆-trans w w') w'')
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  (_R_               : (Γ Δ : C) → Set)
  (factor            : ∀ {Γ Δ Δ' : C} → (r : Γ R Δ) → (w : Δ ⊆ Δ') → ∃ λ Γ' → Γ ⊆ Γ' ∧ Γ' R Δ')
  (let lCtx          : {Γ Δ Δ' : C} → (r : Γ R Δ) → (w : Δ ⊆ Δ') → C    ; lCtx     = λ r w → factor r w .fst)
  (let factorWk      : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → Γ ⊆ _  ; factorWk = λ r w → factor r w .snd .fst)
  (let factorR       : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → _ R Δ' ; factorR  = λ r w → factor r w .snd .snd)
  (factor-pres-refl  : ∀ {Γ Δ : C} (r : Γ R Δ) → factor r ⊆-refl ≡ (-, ⊆-refl , r))
  (factor-pres-trans : ∀ {Γ Δ Δ' Δ''} (r : Γ R Δ) (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') → factor r (⊆-trans w w') ≡ (-, ⊆-trans (factorWk r w) (factorWk (factorR r w) w') , factorR (factorR r w) w'))
  where

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans

private
  variable
    Γ Γ' Γ'' : C
    Δ Δ' Δ'' : C
    Θ Θ' Θ'' : C
    w w' w'' : Γ ⊆ Δ
    𝒫 𝒫'     : Psh
    𝒬 𝒬'     : Psh
    ℛ ℛ' ℛ'' : Psh
    s s'     : 𝒫 →̇ 𝒬
    t t'     : 𝒫 →̇ 𝒬
    u u'     : 𝒫 →̇ 𝒬

record ✦'-Fam (𝒫 : Psh) (Γ : C) : Set where
  constructor elem
  field
    elem : Σ λ Δ → Δ R Γ × 𝒫 ₀ Δ

record _✦'-≋_ {𝒫 : Psh} {Γ : C} (x x' : ✦'-Fam 𝒫 Γ) : Set where
  constructor proof
  field
    proof : let elem (Δ , r , p) = x; elem (Δ' , r' , p') = x' in ∃ λ Δ≡Δ' → subst (_R _) Δ≡Δ' r ≡ r' ∧ subst (𝒫 ₀_) Δ≡Δ' p ≋[ 𝒫 ] p'

✦'_ : (𝒫 : Psh) → Psh -- type \blacklozenge
✦' 𝒫 = record
  { Fam           = ✦'-Fam 𝒫
  ; _≋_           = _✦'-≋_
  ; ≋-equiv       = ≋-equiv
  ; wk            = wk
  ; wk-pres-≋     = wk-pres-≋
  ; wk-pres-refl  = wk-pres-refl
  ; wk-pres-trans = wk-pres-trans
  }
  where
    abstract
      ≋-equiv : (Γ : C) → IsEquivalence (_✦'-≋_ {𝒫} {Γ})
      ≋-equiv = λ Γ → record
        { refl  = proof (refl , refl , ≋[ 𝒫 ]-refl)
        ; sym   = λ { (proof (refl , r≡r' , p≋p')) → proof (refl , sym r≡r' , ≋[ 𝒫 ]-sym p≋p') }
        ; trans = λ { (proof (refl , r≡r' , p≋p')) (proof (refl , r'≡r'' , p'≋p'')) → proof (refl , trans r≡r' r'≡r'' , ≋[ 𝒫 ]-trans p≋p' p'≋p'') }
        }

    wk : (w : Γ ⊆ Γ') → (x : ✦'-Fam 𝒫 Γ) → ✦'-Fam 𝒫 Γ'
    wk w (elem (Δ , r , p)) = let (Δ' , w' , r') = factor r w in elem (Δ' , r' , wk[ 𝒫 ] w' p)

    abstract
      wk-pres-≋ : ∀ (w : Γ ⊆ Γ') {x x' : ✦'-Fam 𝒫 Γ} (x≋x' : x ✦'-≋ x') → wk w x ✦'-≋ wk w x'
      wk-pres-≋ w (proof (refl , refl , p≋p')) = proof (refl , refl , wk[ 𝒫 ]-pres-≋ _ p≋p')

      wk-pres-refl : ∀ (x : ✦'-Fam 𝒫 Γ) → wk ⊆-refl x ✦'-≋ x
      wk-pres-refl {_Γ} x@(elem (_ , r , p)) = subst (λ (Δ' , w' , r') → elem (Δ' , r' , wk[ 𝒫 ] w' p) ✦'-≋ x) (sym (factor-pres-refl r)) (proof (refl , refl , wk[ 𝒫 ]-pres-refl p))

      wk-pres-trans : ∀ (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (x : ✦'-Fam 𝒫 Γ) → wk (⊆-trans w w') x ✦'-≋ wk w' (wk w x)
      wk-pres-trans {_Γ} {_Γ'} {_Γ''} w w' x@(elem (_ , r , p)) = subst (λ (Δ'' , w'' , r'') → elem (Δ'' , r'' , wk[ 𝒫 ] w'' p) ✦'-≋ wk w' (wk w x)) (sym (factor-pres-trans r w w')) (proof (refl , refl , (wk[ 𝒫 ]-pres-trans (factorWk r w) (factorWk (factorR r w) w') p)))

✦'-map_ : (t : 𝒫 →̇ 𝒬) → ✦' 𝒫 →̇ ✦' 𝒬
✦'-map_ {_} {𝒬} t = record
  { fun     = λ (elem (Δ , r , p)) → elem (Δ , r , t .apply p)
  ; pres-≋  = λ { (proof (refl , r≡r' , p≋p')) → proof (refl , r≡r' , t .apply-≋ p≋p') }
  ; natural = λ w (elem (Δ , r , p)) → proof (refl , refl , t .natural _ p)
  }

abstract
  ✦'-map-pres-≈̇ : t ≈̇ t' → ✦'-map t ≈̇ ✦'-map t'
  ✦'-map-pres-≈̇ t≈̇t' = record { proof = λ (elem (_ , _ , p)) → proof (refl , refl , t≈̇t' .apply-≋ p) }

  ✦'-map-pres-id' : ✦'-map id'[ 𝒫 ] ≈̇ id'
  ✦'-map-pres-id' {𝒫} = record { proof = λ p → proof (refl , refl , ≋[ 𝒫 ]-refl) }

  ✦'-map-pres-∘ : ∀ (t' : 𝒬 →̇ ℛ) (t : 𝒫 →̇ 𝒬) → ✦'-map (t' ∘ t) ≈̇ ✦'-map t' ∘ ✦'-map t
  ✦'-map-pres-∘ {ℛ = ℛ} _ _ = record { proof = λ p → proof (refl , refl , ≋[ ℛ ]-refl) }

module IS4
  (R-trans           : ∀ {Γ Δ Θ : C} (r : Γ R Δ) (r' : Δ R Θ) → Γ R Θ)
  (R-trans-assoc     : ∀ {Γ Δ Θ Ξ : C} (r : Γ R Δ) (r' : Δ R Θ) (r'' : Θ R Ξ) → R-trans r (R-trans r' r'') ≡ R-trans (R-trans r r') r'')
  (R-refl            : ∀ {Γ : C} → Γ R Γ)
  (R-refl-unit-left  : ∀ {Γ Δ : C} (r : Γ R Δ) → R-trans r R-refl ≡ r)
  (R-refl-unit-right : ∀ {Γ Δ : C} (r : Γ R Δ) → R-trans R-refl r ≡ r)
  (let lCtx          : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → C      ; lCtx     = λ r w → factor r w .fst)
  (let factorWk      : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → Γ ⊆ _  ; factorWk = λ r w → factor r w .snd .fst)
  (let factorR       : ∀ {Γ Δ Δ' : C} (r : Γ R Δ) (w : Δ ⊆ Δ') → _ R Δ' ; factorR  = λ r w → factor r w .snd .snd)
  (factor-pres-refl  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → factor R-refl w ≡ (Γ' , w , R-refl))
  (factor-pres-trans : ∀ {Γ Δ Θ Θ' : C} (r : Γ R Δ) (r' : Δ R Θ) (w : Θ ⊆ Θ') → factor (R-trans r r') w ≡ (lCtx r (factorWk r' w) , factorWk r _ , R-trans (factorR r _) (factorR r' w)))
  where
    η'[_] : (𝒫 : Psh) → 𝒫 →̇ ✦' 𝒫
    η'[_] 𝒫 = record
      { fun     = λ {Γ} p → elem (Γ , R-refl , p)
      ; pres-≋  = λ p≋p' → proof (refl , refl , p≋p')
      ; natural = λ w p → let open EqReasoning ≋[ ✦' 𝒫 ]-setoid in begin
          elem (-, factorR R-refl w , wk[ 𝒫 ] (factorWk R-refl w) p)
            ≡⟨ cong (λ { (_ , w , r) → elem (-, r , wk[ 𝒫 ] w p) }) (factor-pres-refl w) ⟩
          elem (-, R-refl , wk[ 𝒫 ] w p)
            ∎
      }

    abstract
      η'-nat : ∀ (φ : 𝒫 →̇ 𝒬) → ✦'-map φ ∘ η'[ 𝒫 ] ≈̇ η'[ 𝒬 ] ∘ φ
      η'-nat {_} {𝒬} φ = record { proof = λ p → proof (refl , refl , ≋[ 𝒬 ]-refl) }

    μ'[_] : (𝒫 : Psh) → ✦' ✦' 𝒫 →̇ ✦' 𝒫
    μ'[_] 𝒫 = record
      { fun     = λ (elem (Δ , r' , elem (Γ , r , p))) → elem (Γ , R-trans r r' , p)
      ; pres-≋  = λ { (proof (refl , refl , proof (refl , refl , p≋p'))) → proof (refl , refl , p≋p') }
      ; natural = λ w (elem (Δ , r' , elem (Γ , r , p))) → let open EqReasoning ≋[ ✦' 𝒫 ]-setoid in begin
          elem (-, factorR (R-trans r r') w , wk[ 𝒫 ] (factorWk (R-trans r r') w) p)
            ≡⟨ cong (λ { (_ , w , r) → elem (-, r , wk[ 𝒫 ] w p) }) (factor-pres-trans r r' w) ⟩
          elem (-, R-trans (factorR r (factorWk r' w)) (factorR r' w) , wk[ 𝒫 ] (factorWk r (factorWk r' w)) p)
            ∎
      }

    abstract
      μ'-nat : ∀ (φ : 𝒫 →̇ 𝒬) → ✦'-map φ ∘ μ'[ 𝒫 ] ≈̇ μ'[ 𝒬 ] ∘ ✦'-map ✦'-map φ
      μ'-nat {_} {𝒬} φ = record { proof = λ p → proof (refl , refl , ≋[ 𝒬 ]-refl) }

      η'-unit-left[_] : ∀ (𝒫 : Psh) → μ'[ 𝒫 ] ∘ η'[ ✦' 𝒫 ] ≈̇ id'[ ✦' 𝒫 ]
      η'-unit-left[_] 𝒫 = record { proof = λ (elem (_ , r , p)) → proof (refl , R-refl-unit-left r , ≋[ 𝒫 ]-refl) }

      η'-unit-right[_] : ∀ (𝒫 : Psh) → μ'[ 𝒫 ] ∘ ✦'-map η'[ 𝒫 ] ≈̇ id'[ ✦' 𝒫 ]
      η'-unit-right[_] 𝒫 = record { proof = λ (elem (_ , r , p)) → proof (refl , R-refl-unit-right r , ≋[ 𝒫 ]-refl) }

      μ'-assoc[_] : ∀ (𝒫 : Psh) → μ'[ 𝒫 ] ∘ μ'[ ✦' 𝒫 ] ≈̇ μ'[ 𝒫 ] ∘ ✦'-map μ'[ 𝒫 ]
      μ'-assoc[_] 𝒫 = record { proof = λ (elem (_ , r'' , elem (_ , r' , elem (_ , r , p)))) → proof (refl , R-trans-assoc r r' r'' , ≋[ 𝒫 ]-refl) }

    η'            = λ {𝒫} → η'[ 𝒫 ]
    μ'            = λ {𝒫} → μ'[ 𝒫 ]
    η'-unit-left  = λ {𝒫} → η'-unit-left[ 𝒫 ]
    η'-unit-right = λ {𝒫} → η'-unit-right[ 𝒫 ]
    μ'-assoc      = λ {𝒫} → μ'-assoc[ 𝒫 ]

module _ (𝒫 : Psh) where
  -- Fam : (Γ : C) → Set where
  -- Fam = λ Γ → {Δ : C} → (r : Γ R Δ) → 𝒫 ₀ Δ
  record □'-Fam (Γ : C) : Set where
    constructor elem
    field
      fun     : {Γ' Δ : C} → (w : Γ ⊆ Γ') → (r : Γ' R Δ) → 𝒫 ₀ Δ
      natural : ∀ {Γ' Δ Δ' : C} (w : Γ ⊆ Γ') (r : Γ' R Δ) (w' : Δ ⊆ Δ') → fun (⊆-trans w (factorWk r w')) (factorR r w') ≋[ 𝒫 ] wk[ 𝒫 ] w' (fun w r)

  open □'-Fam using (natural) renaming (fun to apply) public

module _ {𝒫 : Psh} where
  -- _≋_ : {Γ : C} → (x x' : □'-Fam Γ) → Set
  -- _≋_ {Γ} = λ x y → ∀ {Δ : C} {r r' : Γ R Δ} (r≡r' : r ≡ r') → x r ≋[ 𝒫 ] y r'
  record _□'-≋_ {Γ : C} (x x' : □'-Fam 𝒫 Γ) : Set where
    constructor proof
    field
      pw : ∀ {Γ' Δ : C} (w : Γ ⊆ Γ') (r : Γ' R Δ) → x .apply w r ≋[ 𝒫 ] x' .apply w r

  open _□'-≋_ using (pw) public

module _ (𝒫 : Psh) where
  □'_ : Psh -- type \Box
  □'_ = record
    { Fam           = □'-Fam 𝒫
    ; _≋_           = _□'-≋_
    ; ≋-equiv       = ≋-equiv
    ; wk            = wk
    ; wk-pres-≋     = wk-pres-≋
    ; wk-pres-refl  = wk-pres-refl
    ; wk-pres-trans = wk-pres-trans
    }
    where
      abstract
        ≋-equiv : (Γ : C) → IsEquivalence (_□'-≋_ {𝒫} {Γ})
        ≋-equiv = λ Γ → record
          { refl  = record { pw = λ _w _r → ≋[ 𝒫 ]-refl }
          ; sym   = λ x≋x' → record { pw = λ w r → ≋[ 𝒫 ]-sym (x≋x' .pw w r) }
          ; trans = λ x≋x' x'≋x'' → record { pw = λ w r → ≋[ 𝒫 ]-trans (x≋x' .pw w r) (x'≋x'' .pw w r) }
          }

      wk : (w : Γ ⊆ Γ') → (x : □'-Fam 𝒫 Γ) → □'-Fam 𝒫 Γ'
      wk w x = record
        { fun     = λ w' r → x .apply (⊆-trans w w') r
        ; natural = λ w' r w'' → let open EqReasoning ≋[ 𝒫 ]-setoid in begin
            x .apply (⊆-trans w (⊆-trans w' (factorWk r w''))) (factorR r w'')  ≡⟨ cong (λ hole → x .apply hole (factorR r w'')) (⊆-trans-assoc w w' (factorWk r w'')) ⟩
            x .apply (⊆-trans (⊆-trans w w') (factorWk r w'')) (factorR r w'')  ≈⟨ x .natural (⊆-trans w w') r w'' ⟩
            wk[ 𝒫 ] w'' (x .apply (⊆-trans w w') r)                             ∎
        }

      abstract
        wk-pres-≋ : ∀ (w : Γ ⊆ Γ') {x x' : □'-Fam 𝒫 Γ} (x≋x' : x □'-≋ x') → wk w x □'-≋ wk w x'
        wk-pres-≋ w x≋x' = record { pw = λ w' r → x≋x' .pw (⊆-trans w w') r }

        wk-pres-refl : ∀ (x : □'-Fam 𝒫 Γ) → wk ⊆-refl x □'-≋ x
        wk-pres-refl {_Γ} x = record { pw = λ {_Γ'} w r → ≋[ 𝒫 ]-reflexive (cong (λ hole → x .apply hole r) (⊆-refl-unit-right w)) }

        wk-pres-trans : ∀ (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (x : □'-Fam 𝒫 Γ) → wk (⊆-trans w w') x □'-≋ wk w' (wk w x)
        wk-pres-trans {_Γ} {_Γ'} {_Γ''} w w' x = record { pw = λ {_Γ'''} w'' r → ≋[ 𝒫 ]-reflexive˘ (cong (λ hole → x .apply hole r) (⊆-trans-assoc w w' w'')) }

□'-map_ : (t : 𝒫 →̇ 𝒬) → □' 𝒫 →̇ □' 𝒬
□'-map_ {𝒫} {𝒬} t = record
  { fun     = λ x → record
      { fun     = λ w r → t .apply (x .apply w r)
      ; natural = λ w r w' → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
          t .apply (x .apply (⊆-trans w (factorWk r w')) (factorR r w'))  ≈⟨ t .apply-≋ (x .natural w r w') ⟩
          t .apply (wk[ 𝒫 ] w' (x .apply w r))                            ≈˘⟨ t .natural w' (x .apply w r) ⟩
          wk[ 𝒬 ] w' (t .apply (x .apply w r))                            ∎
      }
  ; pres-≋  = λ x≋x' → record { pw = λ w r → t .apply-≋ (x≋x' .pw w r) }
  ; natural = λ _w _x → record { pw = λ _w' _r → ≋[ 𝒬 ]-refl }
  }

module _ {𝒫 𝒬 : Psh} where
  box' : (t : ✦' 𝒫 →̇ 𝒬) → 𝒫 →̇ □' 𝒬
  box' t = record
    { fun     = λ p → record
        { fun     = λ w r → t .apply (elem (_ , r , wk[ 𝒫 ] w p))
        ; natural = λ w r w' → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
            t .apply (elem (_ , factorR r w' , wk[ 𝒫 ] (⊆-trans w (factorWk r w')) p))  ≈⟨ t .apply-≋ (proof (refl , refl , wk[ 𝒫 ]-pres-trans w (factorWk r w') p)) ⟩
            t .apply (elem (_ , factorR r w' , wk[ 𝒫 ] (factorWk r w') (wk[ 𝒫 ] w p)))  ≡⟨⟩
            t .apply (wk[ ✦' 𝒫 ] w' (elem (_ , r , wk[ 𝒫 ] w p)))                       ≈˘⟨ t .natural w' (elem (_ , r , wk[ 𝒫 ] w p)) ⟩
            wk[ 𝒬 ] w' (t .apply (elem (_ , r , wk[ 𝒫 ] w p)))                          ∎
        }
    ; pres-≋  = λ p≋p' → record { pw = λ w r  → t .apply-≋ (proof (refl , refl , wk[ 𝒫 ]-pres-≋ w p≋p')) }
    ; natural = λ w p → record
        { pw = λ w' r → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
            t .apply (elem (_ , r , wk[ 𝒫 ] (⊆-trans w w') p))  ≈⟨ t .apply-≋ (proof (refl , refl , wk[ 𝒫 ]-pres-trans w w' p)) ⟩
            t .apply (elem (_ , r , wk[ 𝒫 ] w' (wk[ 𝒫 ] w p)))  ∎
        }
    }

  abstract
    box'-pres-≈̇ : t ≈̇ t' → box' t ≈̇ box' t'
    box'-pres-≈̇ t≈̇t' = record { proof = λ p → record { pw = λ w r → t≈̇t' .apply-≋ (elem (_ , _ , wk[ 𝒫 ] w p)) } }

λ' : (t : 𝒫 →̇ □' 𝒬) → ✦' 𝒫 →̇ 𝒬
λ' {𝒫} {𝒬} t = record
  { fun     = λ (elem (_ , r , p)) → t .apply p .apply ⊆-refl r
  ; pres-≋  = λ { (proof (refl , refl , p≋p')) → t .apply-≋ p≋p' .pw ⊆-refl _ }
  ; natural = λ w (elem (_ , r , p)) → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
      wk[ 𝒬 ] w (t .apply p .apply ⊆-refl r)                              ≈˘⟨ t .apply p .natural ⊆-refl r w ⟩
      t .apply p .apply (⊆-trans ⊆-refl (factorWk r w)) (factorR r w)     ≡⟨ cong (λ hole → t .apply p .apply hole (factorR r w)) (⊆-refl-unit-right (factorWk r w)) ⟩
      t .apply p .apply (factorWk r w) (factorR r w)                      ≡˘⟨ cong (λ hole → t .apply p .apply hole (factorR r w)) (⊆-refl-unit-left (factorWk r w)) ⟩
      t .apply p .apply (⊆-trans (factorWk r w) ⊆-refl) (factorR r w)     ≡⟨⟩
      wk[ □' 𝒬 ] (factorWk r w) (t .apply p) .apply ⊆-refl (factorR r w)  ≈⟨ t .natural (factorWk r w) p .pw ⊆-refl (factorR r w) ⟩
      t .apply (wk[ 𝒫 ] (factorWk r w) p) .apply ⊆-refl (factorR r w)     ∎
  }

abstract
  λ'-pres-≈̇ : t ≈̇ t' → λ' t ≈̇ λ' t'
  λ'-pres-≈̇ t≈̇t' = record { proof = λ (elem (_ , r , p)) → t≈̇t' .apply-≋ p .pw ⊆-refl r }

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
  □'-beta {𝒫} {𝒬} t = record
    { proof = λ (elem (_ , r , p)) → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
        t .apply (elem (_ , r , wk[ 𝒫 ] ⊆-refl p))  ≈⟨ t .apply-≋ (proof (refl , refl , wk[ 𝒫 ]-pres-refl p)) ⟩
        t .apply (elem (_ , r , p))                 ∎
    }

  □'-eta : ∀ (t : 𝒫 →̇ □' 𝒬) → t ≈̇ box' (λ' t)
  □'-eta {𝒫} {𝒬} t = record
    { proof = λ p → record
        { pw = λ w r → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
            t .apply p .apply w r                      ≡˘⟨ cong (λ hole → t .apply p .apply hole r) (⊆-refl-unit-left w) ⟩
            t .apply p .apply (⊆-trans w ⊆-refl) r     ≡⟨⟩
            wk[ □' 𝒬 ] w (t .apply p) .apply ⊆-refl r  ≈⟨ t .natural w p .pw ⊆-refl r ⟩
            t .apply (wk[ 𝒫 ] w p) .apply ⊆-refl r     ∎
        }
    }

  box'-nat-dom : ∀ (t : ✦' 𝒫 →̇ 𝒬) (t' : 𝒫' →̇ 𝒫) → box' (t ∘ ✦'-map t') ≈̇ box' t ∘ t'
  box'-nat-dom {𝒫} {𝒬} {𝒫'} t t' = record
    { proof = λ p' → record
        { pw = λ w r → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
            t .apply (elem (_ , r , t' .apply (wk[ 𝒫' ] w p')))  ≈˘⟨ t .apply-≋ (proof (refl , refl , t' .natural w p')) ⟩
            t .apply (elem (_ , r , wk[ 𝒫 ] w (t' .apply p')))   ∎
        }
    }

  box'-nat-cod : ∀ (t' : 𝒬 →̇ 𝒬') (t : ✦' 𝒫 →̇ 𝒬) → box' (t' ∘ t) ≈̇ □'-map t' ∘ box' t
  box'-nat-cod {𝒬' = 𝒬'} _t' _t = record { proof = λ _p → record { pw = λ _w _r → ≋[ 𝒬' ]-refl } }

  λ'-nat-dom : ∀ (t : 𝒫 →̇ □' 𝒬) (t' : 𝒫' →̇ 𝒫) → λ' (t ∘ t') ≈̇ λ' t ∘ ✦'-map t'
  λ'-nat-dom {𝒬 = 𝒬} _t _t' = record { proof = λ (elem (_Δ , _r , _p')) → ≋[ 𝒬 ]-refl }

  λ'-nat-cod : ∀ (t' : 𝒬 →̇ 𝒬') (t : 𝒫 →̇ □' 𝒬) → λ' (□'-map t' ∘ t) ≈̇ t' ∘ λ' t
  λ'-nat-cod {𝒬' = 𝒬'} _t' _t = record { proof = λ (elem (_Δ , _r , _p)) → ≋[ 𝒬' ]-refl }

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
