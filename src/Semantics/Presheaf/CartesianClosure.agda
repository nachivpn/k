open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

module Semantics.Presheaf.CartesianClosure
  (C                 : Set)
  (_⊆_               : (Γ Γ' : C) → Set)
  (⊆-trans           : ∀ {Γ Γ' Γ'' : C} → (w : Γ ⊆ Γ') → (w' : Γ' ⊆ Γ'') → Γ ⊆ Γ'')
  (⊆-trans-assoc     : ∀ {Γ Γ' Γ'' Γ''' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (w'' : Γ'' ⊆ Γ''') → ⊆-trans w (⊆-trans w' w'') ≡ ⊆-trans (⊆-trans w w') w'')
  (⊆-refl            : ∀ {Γ : C} → Γ ⊆ Γ)
  (⊆-refl-unit-left  : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans w ⊆-refl ≡ w)
  (⊆-refl-unit-right : ∀ {Γ Γ' : C} (w : Γ ⊆ Γ') → ⊆-trans ⊆-refl w ≡ w)
  where

open import Data.Unit using (⊤; tt)
open import Data.Unit.Properties using () renaming (⊤-irrelevant to ⊤-eta)

open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Product using () renaming (_×_ to _∧_)

open import Function using (id)

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Properties using () renaming (isEquivalence to ≡-equiv)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Semantics.Presheaf.Base C _⊆_ ⊆-refl ⊆-trans

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
  { Fam           = λ _Γ → ⊤
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _Γ → ≡-equiv
  ; wk            = λ _w → id
  ; wk-pres-≋     = λ _w → cong id
  ; wk-pres-refl  = λ _x → ≡-refl
  ; wk-pres-trans = λ _x _w _w' → ≡-refl
  }

[]' = Unit'

unit' : ℛ →̇ Unit'
unit' = record
  { fun     = λ _r → tt
  ; pres-≋  = λ {Γ} _p≋p' → ≋[ Unit' ]-refl {Γ}
  ; natural = λ {_Γ} {Δ} _w _r → ≋[ Unit' ]-refl {Δ}
  }

unit'[_] = λ ℛ → unit' {ℛ}

Unit'-eta : t ≈̇ unit'
Unit'-eta {ℛ} {t} = record { proof = λ r → ⊤-eta (t .apply r) (unit'[ ℛ ] .apply r) }

[]'-eta = Unit'-eta

module _ (𝒫 𝒬 : Psh) where
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  record Fam (Γ : C) : Set where
    constructor elem
    field
      elem : P Γ × Q Γ

  record _≋_ {Γ : C} (x y : Fam Γ) : Set where
    constructor proof
    field
      proof : let elem (p , q) = x; elem (p' , q') = y in p ≋[ 𝒫 ] p' ∧ q ≋[ 𝒬 ] q'

  private
    ≋-equiv : ∀ (Γ : C) → IsEquivalence (_≋_ {Γ})
    ≋-equiv _Γ = record
      { refl  = proof (≋[ 𝒫 ]-refl , ≋[ 𝒬 ]-refl)
      ; sym   = λ (proof (p≋p' , q≋q')) → proof (≋[ 𝒫 ]-sym p≋p' , ≋[ 𝒬 ]-sym q≋q')
      ; trans = λ (proof (p≋p' , q≋q')) (proof (p'≋p'' , q'≋q'')) → proof (≋[ 𝒫 ]-trans p≋p' p'≋p'' , ≋[ 𝒬 ]-trans q≋q' q'≋q'')
      }

  _×'_ : Psh
  _×'_ = record
    { Fam           = Fam
    ; _≋_           = _≋_
    ; ≋-equiv       = ≋-equiv
    ; wk            = λ w (elem (p , q)) → elem (wk[ 𝒫 ] w p , wk[ 𝒬 ] w q)
    ; wk-pres-≋     = λ w (proof (p≋p' , q≋q')) → proof (wk[ 𝒫 ]-pres-≋ w p≋p' , wk[ 𝒬 ]-pres-≋ w q≋q')
    ; wk-pres-refl  = λ (elem (p , q)) → proof (wk[ 𝒫 ]-pres-refl p , wk[ 𝒬 ]-pres-refl q)
    ; wk-pres-trans = λ w w' (elem (p , q)) → proof (wk[ 𝒫 ]-pres-trans w w' p , wk[ 𝒬 ]-pres-trans w w' q)
    }

module _ {𝒫 𝒬 : Psh} where
  π₁' : 𝒫 ×' 𝒬 →̇ 𝒫
  π₁' = record
    { fun     = λ x → let elem (p , _q) = x in p
    ; pres-≋  = λ x≋y → let proof (p≋p' , _q≋q') = x≋y in p≋p'
    ; natural = λ _w x → let elem (_p , _q) = x in ≋[ 𝒫 ]-refl
    }

  π₂' : 𝒫 ×' 𝒬 →̇ 𝒬
  π₂' = record
    { fun     = λ x → let elem (_p , q) = x in q
    ; pres-≋  = λ x≋y → let proof (_p≋p' , q≋q') = x≋y in q≋q'
    ; natural = λ _w x → let elem (_p , _q) = x in ≋[ 𝒬 ]-refl
    }

  fst' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒫
  fst' = π₁' ∘_

  snd' : (t : ℛ →̇ 𝒫 ×' 𝒬) → ℛ →̇ 𝒬
  snd' = π₂' ∘_

  pr' : (t : ℛ →̇ 𝒫) → (u : ℛ →̇ 𝒬) → ℛ →̇ 𝒫 ×' 𝒬
  pr' t u = record
    { fun     = λ r → elem (t .apply r , u .apply r)
    ; pres-≋  = λ r≋r' → proof (t .apply-≋ r≋r' , u .apply-≋ r≋r')
    ; natural = λ w r → proof (t .natural w r , u .natural w r)
    }

  ⟨_,_⟩' = pr'

  abstract
    pr'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → pr' t u ≈̇ pr' t' u'
    pr'-pres-≈̇ t≈̇t' u≈̇u' = record { proof = λ r → proof (t≈̇t' .apply-≋ r , u≈̇u' .apply-≋ r) }

    ⟨,⟩'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → ⟨ t , u ⟩' ≈̇ ⟨ t' , u' ⟩'
    ⟨,⟩'-pres-≈̇ = pr'-pres-≈̇

    pr'-pres-≈̇-left : t ≈̇ t' → pr' t u ≈̇ pr' t' u
    pr'-pres-≈̇-left {u = u} t≈̇t' = pr'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    pr'-pres-≈̇-right : u ≈̇ u' → pr' t u ≈̇ pr' t u'
    pr'-pres-≈̇-right {t = t} u≈̇u' = pr'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

    pr'-nat : ∀ (t : ℛ →̇ 𝒫) (u : ℛ →̇ 𝒬) (s : ℛ' →̇ ℛ) → pr' t u ∘ s ≈̇ pr' (t ∘ s) (u ∘ s)
    pr'-nat _t _u _s = ≈̇-refl

    ⟨,⟩'-nat : ∀ (t : ℛ →̇ 𝒫) (u : ℛ →̇ 𝒬) (s : ℛ' →̇ ℛ) → ⟨ t , u ⟩' ∘ s ≈̇ ⟨ t ∘ s , u ∘ s ⟩'
    ⟨,⟩'-nat _t _u _s = ≈̇-refl

    ×'-beta-left : ∀ {t : ℛ →̇ 𝒫} (u : ℛ →̇ 𝒬) → fst' (pr' t u) ≈̇ t
    ×'-beta-left {_t} _u = record { proof = λ _r → ≋[ 𝒫 ]-refl }

    ×'-beta-right : ∀ (t : ℛ →̇ 𝒫) {u : ℛ →̇ 𝒬} → snd' (pr' t u) ≈̇ u
    ×'-beta-right t {_u} = record { proof = λ _r → ≋[ 𝒬 ]-refl }

    ×'-eta : t ≈̇ pr' (fst' t) (snd' t)
    ×'-eta = record { proof = λ _r → ≋[ 𝒫 ×' 𝒬 ]-refl }

π₁'[_] = λ {𝒫} 𝒬 → π₁' {𝒫} {𝒬}

π₁'[_][_] = λ 𝒫 𝒬 → π₁' {𝒫} {𝒬}

π₂'[_] = λ 𝒫 {𝒬} → π₂' {𝒫} {𝒬}

π₂'[_][_] = λ 𝒫 𝒬 → π₂' {𝒫} {𝒬}

_×'-map_ : (t : 𝒫 →̇ 𝒫') → (u : 𝒬 →̇ 𝒬') → 𝒫 ×' 𝒬 →̇ 𝒫' ×' 𝒬'
_×'-map_ {𝒫 = 𝒫} {𝒬 = 𝒬} t u = pr' (t ∘ π₁'[ 𝒬 ]) (u ∘ π₂'[ 𝒫 ])

abstract
  ×'-map-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → t ×'-map u ≈̇ t' ×'-map u'
  ×'-map-pres-≈̇ t≈̇t' u≈̇u' = record { proof = λ x → let elem (p , q) = x in proof (t≈̇t' .apply-≋ p , u≈̇u' .apply-≋ q) }

  ×'-map-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : 𝒬 →̇ 𝒬') → t ×'-map u ≈̇ t' ×'-map u
  ×'-map-pres-≈̇-left t≈̇t' u = ×'-map-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

  ×'-map-pres-≈̇-right : ∀ (t : 𝒫 →̇ 𝒫') (_ : u ≈̇ u') → t ×'-map u ≈̇ t ×'-map u'
  ×'-map-pres-≈̇-right t u≈̇u' = ×'-map-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

  ×'-map-pres-id : ∀ {𝒫 𝒬 : Psh} → id'[ 𝒫 ] ×'-map id'[ 𝒬 ] ≈̇ id'[ 𝒫 ×' 𝒬 ]
  ×'-map-pres-id {𝒫} {𝒬} = record { proof = λ _x → ≋[ 𝒫 ×' 𝒬 ]-refl }

module _ (𝒫 𝒬 : Psh) where
  open Psh 𝒫 using () renaming (Fam to P)
  open Psh 𝒬 using () renaming (Fam to Q)

  record ⇒'-Fam (Γ : C) : Set where
    constructor elem
    field
      fun     : {Γ' : C} → (w : Γ ⊆ Γ') → P Γ' → Q Γ'
      pres-≋  : ∀ {Γ' : C} → (w : Γ ⊆ Γ') {p p' : P Γ'} → (p≋p' : p ≋[ 𝒫 ] p') → fun w p ≋[ 𝒬 ] fun w p'
      natural : ∀ {Γ' Γ'' : C} (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (p : P Γ') → wk[ 𝒬 ] w' (fun w p) ≋[ 𝒬 ] fun (⊆-trans w w') (wk[ 𝒫 ] w' p)

  open ⇒'-Fam using (natural) renaming (fun to apply; pres-≋ to apply-≋) public

  record _⇒'-≋_ {Γ : C} (f g : ⇒'-Fam Γ) : Set where
    constructor proof
    field
      pw : ∀ {Δ : C} (w : Γ ⊆ Δ) (p : P Δ) → f .apply w p ≋[ 𝒬 ] g .apply w p

  open _⇒'-≋_ using (pw) public

  private
    ⇒'-≋-equiv : ∀ (_Γ : C) → IsEquivalence (_⇒'-≋_ {_Γ})
    ⇒'-≋-equiv _Γ = record
      { refl  = proof (λ _w _p → ≋[ 𝒬 ]-refl)
      ; sym   = λ {f} {g} f≋g → proof (λ w p → ≋[ 𝒬 ]-sym (f≋g .pw w p))
      ; trans = λ {f} {g} {h} f≋g g≋h → proof (λ w p → ≋[ 𝒬 ]-trans (f≋g .pw w p) (g≋h .pw w p))
      }

  _⇒'_ : Psh
  _⇒'_ = record
    { Fam           = ⇒'-Fam
    ; _≋_           = _⇒'-≋_
    ; wk            = λ w f → elem (λ w' p → f .apply (⊆-trans w w') p)
                                   (λ w' p≋p' → f .apply-≋ (⊆-trans w w') p≋p')
                                   (λ w' w'' p → subst (λ hole → wk[ 𝒬 ] w'' (f .apply (⊆-trans w w') p) ≋[ 𝒬 ] f .apply hole (wk[ 𝒫 ] w'' p)) (≡-sym (⊆-trans-assoc w w' w'')) (f .natural (⊆-trans w w') w'' p))
    ; ≋-equiv       = ⇒'-≋-equiv
    ; wk-pres-≋     = λ w f≋g → proof (λ w' → f≋g .pw (⊆-trans w w'))
    ; wk-pres-refl  = λ f → proof (λ w p → ≋[ 𝒬 ]-reflexive (cong (λ hole → f .apply hole p) (⊆-refl-unit-right w)))
    ; wk-pres-trans = λ w w' f → proof (λ w'' p → ≋[ 𝒬 ]-reflexive˘ (cong (λ hole → f .apply hole p) (⊆-trans-assoc w w' w'')))
    }

module _ {𝒫 𝒬 : Psh} where
  private
    ⇒'-≋-apply-sq : ∀ {f g : 𝒫 ⇒' 𝒬 ₀ Γ} (_f≋g : f ≋[ 𝒫 ⇒' 𝒬 ] g) (w : Γ ⊆ Δ) {p p' : 𝒫 ₀ Δ} → (_p≋p' : p ≋[ 𝒫 ] p') → f .apply w p ≋[ 𝒬 ] g .apply w p'
    ⇒'-≋-apply-sq {_Γ} {_Δ} {f} {g} f≋g w {p} {p'} p≋p' = let open EqReasoning ≋[ 𝒬 ]-setoid in begin
      f .apply w p   ≈⟨ f .apply-≋ w p≋p' ⟩
      f .apply w p'  ≈⟨ f≋g .pw w p' ⟩
      g .apply w p'  ∎

  app' : (t : ℛ →̇ 𝒫 ⇒' 𝒬) → (u : ℛ →̇ 𝒫) → ℛ →̇ 𝒬
  app' {ℛ} t u = record
    { fun     = λ r → t .apply r .apply ⊆-refl (u .apply r)
    ; pres-≋  = λ r≋r' → ⇒'-≋-apply-sq (t .apply-≋ r≋r') ⊆-refl (u .apply-≋ r≋r')
    ; natural = λ w r → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
        wk[ 𝒬 ] w (t .apply r .apply ⊆-refl (u .apply r))                   ≈⟨ t .apply r .natural ⊆-refl w (u .apply r) ⟩
        t .apply r .apply (⊆-trans ⊆-refl w) (wk[ 𝒫 ] w (u .apply r))       ≈⟨ t .apply r .apply-≋ (⊆-trans ⊆-refl w) (u .natural w r) ⟩
        t .apply r .apply (⊆-trans ⊆-refl w) (u .apply (wk[ ℛ ] w r))       ≡⟨ cong (λ hole → t .apply r .apply hole (u .apply (wk[ ℛ ] w r))) (⊆-refl-unit-right w) ⟩
        t .apply r .apply w                  (u .apply (wk[ ℛ ] w r))       ≡˘⟨ cong (λ hole → t .apply r .apply hole (u .apply (wk[ ℛ ] w r))) (⊆-refl-unit-left w) ⟩
        t .apply r .apply (⊆-trans w ⊆-refl) (u .apply (wk[ ℛ ] w r))       ≡⟨⟩
        wk[ 𝒫 ⇒' 𝒬 ] w (t .apply r) .apply ⊆-refl (u .apply (wk[ ℛ ] w r))  ≈⟨ t .natural w r .pw ⊆-refl (u .apply (wk[ ℛ ] w r)) ⟩
        t .apply (wk[ ℛ ] w r) .apply ⊆-refl (u .apply (wk[ ℛ ] w r))       ∎
    }

  abstract
    app'-pres-≈̇ : t ≈̇ t' → u ≈̇ u' → app' t u ≈̇ app' t' u'
    app'-pres-≈̇ t≈̇t' u≈̇u' = record { proof = λ r → ⇒'-≋-apply-sq (t≈̇t' .apply-≋ r) ⊆-refl (u≈̇u' .apply-≋ r) }

    app'-pres-≈̇-left : ∀ (_ : t ≈̇ t') (u : ℛ →̇ 𝒫) → app' t u ≈̇ app' t' u
    app'-pres-≈̇-left t≈̇t' u = app'-pres-≈̇ t≈̇t' (≈̇-refl {x = u})

    app'-pres-≈̇-right : ∀ (t : ℛ →̇ 𝒫 ⇒' 𝒬) (_ : u ≈̇ u') → app' t u ≈̇ app' t u'
    app'-pres-≈̇-right t u≈̇u' = app'-pres-≈̇ (≈̇-refl {x = t}) u≈̇u'

    app'-nat : ∀ (t : ℛ →̇ 𝒫 ⇒' 𝒬) (u : ℛ →̇ 𝒫) (s : ℛ' →̇ ℛ) → app' t u ∘ s ≈̇ app' (t ∘ s) (u ∘ s)
    app'-nat _t _u _s = record { proof = λ _r' → ≋[ 𝒬 ]-refl }

lam' : (t : ℛ ×' 𝒫 →̇ 𝒬) → ℛ →̇ 𝒫 ⇒' 𝒬
lam' {ℛ} {𝒫} {𝒬} t = record
  { fun     = λ r → record
                { fun     = λ w p → t .apply (elem (wk[ ℛ ] w r , p))
                ; pres-≋  = λ w p≋p' → t .apply-≋ (proof (≋[ ℛ ]-refl , p≋p'))
                ; natural = λ w w' p → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
                    wk[ 𝒬 ] w' (t .apply (elem (wk[ ℛ ] w r , p)))             ≈⟨ t .natural w' (elem (wk[ ℛ ] w r , p)) ⟩
                    t .apply (elem (wk[ ℛ ] w' (wk[ ℛ ] w r) , wk[ 𝒫 ] w' p))  ≈˘⟨ t .apply-≋ (proof (wk[ ℛ ]-pres-trans w w' r , ≋[ 𝒫 ]-refl)) ⟩
                    t .apply (elem (wk[ ℛ ] (⊆-trans w w') r , wk[ 𝒫 ] w' p))  ∎
                }
  ; pres-≋  = λ r≋r' → proof λ w p → t .apply-≋ (proof (wk[ ℛ ]-pres-≋ w r≋r' , ≋[ 𝒫 ]-refl))
  ; natural = λ w r → proof λ w' p → t .apply-≋ (proof ((wk[ ℛ ]-pres-trans w w' r) , ≋[ 𝒫 ]-refl))
  }

abstract
    lam'-pres-≈̇ : t ≈̇ t' → lam' t ≈̇ lam' t'
    lam'-pres-≈̇ {_𝒬} {ℛ} {𝒫} t≈̇t' = record { proof = λ r → proof (λ w p → t≈̇t' .apply-≋ (elem (wk[ ℛ ] w r , p))) }

    lam'-nat : ∀ (t : ℛ ×' 𝒫 →̇ 𝒬) (s : ℛ' →̇ ℛ) → lam' t ∘ s ≈̇ lam' (t ∘ s ×'-map id'[ 𝒫 ])
    lam'-nat {_ℛ} {𝒫} {_𝒬} {_ℛ'} t s = record { proof = λ r' → proof (λ w p → t .apply-≋ (proof ((s .natural w r') , ≋[ 𝒫 ]-refl))) }

    ⇒'-beta : ∀ (t : ℛ ×' 𝒫 →̇ 𝒬) (u : ℛ →̇ 𝒫) → app' (lam' t) u ≈̇ t [ pr' id' u ]'
    ⇒'-beta {ℛ} {𝒫} t u = record { proof = λ r → t .apply-≋ (proof (wk[ ℛ ]-pres-refl r , ≋[ 𝒫 ]-refl)) }

    ⇒'-eta : ∀ (t : ℛ →̇ 𝒫 ⇒' 𝒬) → t ≈̇ lam' {𝒬 = 𝒬} (app' (t [ π₁'[ 𝒫 ] ]') π₂'[ ℛ ])
    ⇒'-eta {ℛ} {𝒫} {𝒬} t = record
      { proof = λ r → proof (λ w p → let open EqReasoning ≋[ 𝒬 ]-setoid in begin
                               t .apply r .apply w p                        ≡˘⟨ cong (λ hole → t .apply r .apply hole p) (⊆-refl-unit-left w) ⟩
                               t .apply r .apply (⊆-trans w ⊆-refl) p       ≡⟨⟩
                               wk[ 𝒫 ⇒' 𝒬 ] w (t .apply r) .apply ⊆-refl p  ≈⟨ t .natural w r .pw ⊆-refl p ⟩
                               t .apply (wk[ ℛ ] w r) .apply ⊆-refl p       ∎
                            )
      }
