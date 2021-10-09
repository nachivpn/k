module IS4.NbE.Model where

open import Data.Product using (∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)
open import Data.Product.Properties using (Σ-≡,≡↔≡; ×-≡,≡↔≡)

open import Function using (Inverse)

open import Relation.Binary using (Reflexive; Transitive; Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂; cong-id; subst-application) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; isEquivalence to ≡-equiv)

open import IS4.Term as Term hiding (factor2)

import Semantics.Presheaf.Evaluation.IS4

private
  Σ-≡,≡→≡ : {A : Set} {B : A → Set} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : ∃ B} → (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂) → p₁ ≡ p₂
  Σ-≡,≡→≡ = Σ-≡,≡↔≡ .Inverse.f

  ×-≡,≡→≡ : {A B : Set} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A ∧ B} → a₁ ≡ a₂ ∧ b₁ ≡ b₂ → p₁ ≡ p₂
  ×-≡,≡→≡ = ×-≡,≡↔≡ .Inverse.f

  subst-application′ : ∀ {A : Set} {P Q : A → Set} (f : ∀ x → P x → Q x) {x y : A} (p : x ≡ y) (z : P x) → f y (subst P p z) ≡ subst Q p (f x z)
  subst-application′ {P = P} f p z = ≡-trans (cong (λ p → f _ (subst P p z)) (≡-sym (cong-id p))) (≡-sym (subst-application P f p))

  Σ×-≡,≡,≡→≡ : {A : Set} {B B' : A → Set} {p₁@(a₁ , b₁ , b₁') p₂@(a₂ , b₂ , b₂') : ∃ λ (a : A) → B a ∧ B' a} → (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂ ∧ subst B' p b₁' ≡ b₂') → p₁ ≡ p₂
  Σ×-≡,≡,≡→≡ {A} {_B} {_B'} {p₁} {p₂} (p , q , q') = Σ-≡,≡→≡ (p , ×-≡,≡→≡ (≡-trans (subst-application′ (λ (_a : A) → fst) p (snd p₁)) q , ≡-trans (subst-application′ (λ (_a : A) → snd) p (snd p₁)) q'))

_R_ = λ Γ Δ → ∃ λ Γ' → CExt Δ Γ Γ'

variable
  r r' r'' : Γ R Δ

pattern nilR     = _ , nil
pattern extR e   = _ , ext e
pattern ext🔒R e = _ , ext🔒- e

private
  R-refl : Reflexive _R_
  R-refl = nilR

  R-trans : Transitive _R_
  R-trans (_ , ΓRΔ) (_ , ΔRΘ) = -, extRAssoc ΓRΔ ΔRΘ

  R-irrel : Irrelevant _R_
  R-irrel (ΔR , ΓRΔ) (ΔR' , ΓRΔ') = Σ-≡,≡→≡ (extRUniq ΓRΔ ΓRΔ' , ExtIsProp _ _)

  R-trans-assoc : ∀ (r : Γ R Δ) (r' : Δ R Θ) (r'' : Θ R Ξ) → R-trans r (R-trans r' r'') ≡ R-trans (R-trans r r') r''
  R-trans-assoc _ _ _ = R-irrel _ _

  R-refl-unit-left : ∀ (r : Γ R Δ) → R-trans r R-refl ≡ r
  R-refl-unit-left _ = R-irrel _ _

  R-refl-unit-right : ∀ (r : Γ R Δ) → R-trans R-refl r ≡ r
  R-refl-unit-right _ = R-irrel _ _

-- factor1 : ∀ (w : Γ ⊆ Γ') (r : Γ' R Δ') → ∃ λ Δ → Γ R Δ ∧ Δ ⊆ Δ'
-- factor1 w (_ , ΓRΔ) = -, (-, factor1Ext ΓRΔ w) , factor1≤ ΓRΔ w

-- factor1⊆ : ∀ (w : Γ ⊆ Γ') (r : Γ' R Δ') → _ ⊆ Δ'
-- factor1⊆ w r = factor1 w r .snd .snd

-- factor1R : ∀ (w : Γ ⊆ Γ') (r : Γ' R Δ') → Γ R _
-- factor1R w r = factor1 w r .snd .fst

factor2 : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') → ∃ λ Γ' → Γ ⊆ Γ' ∧ Γ' R Δ'
factor2 (_ , ΓRΔ) w = -, factor2≤ ΓRΔ w , -, factor2Ext ΓRΔ w

factor2⊆ : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') → Γ ⊆ _
factor2⊆ r w = factor2 r w .snd .fst

factor2R : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') → _ R Δ'
factor2R r w = factor2 r w .snd .snd

private
  factor2-pres-id : ∀ (r : Γ R Δ) → factor2 r idWk ≡ (-, idWk , r)
  factor2-pres-id (_ , ΓRΔ) = Σ×-≡,≡,≡→≡ (f2LCtxPresId ΓRΔ , factor2≤PresId ΓRΔ , R-irrel _ _)

  factor2-pres-∙ : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') → factor2 r (w ∙ w') ≡ (-, factor2⊆ r w ∙ factor2⊆ (factor2R r w) w' , factor2R (factor2R r w) w')
  factor2-pres-∙ (_ , ΓRΔ) w w' = Σ×-≡,≡,≡→≡ (f2LCtxPres∙ ΓRΔ w w' , factor2≤Pres∙ ΓRΔ w w' , R-irrel _ _)

  factor2-pres-refl : ∀ (w : Γ ⊆ Γ') → factor2 R-refl w ≡ (-, w , R-refl)
  factor2-pres-refl w = Σ-≡,≡→≡ (f2LCtxPresRefl w , ×-≡,≡→≡ (factor2≤PresRefl w , R-irrel _ _))

  factor2-pres-trans : ∀ (r : Γ R Δ) (r' : Δ R Θ) (w : Θ ⊆ Θ') → factor2 (R-trans r r') w ≡ (-, factor2⊆ r (factor2⊆ r' w) , R-trans (factor2R r (factor2⊆ r' w)) (factor2R r' w))
  factor2-pres-trans (_ , ΓRΔ) (_ , ΔRΘ) w = Σ×-≡,≡,≡→≡ (f2LCtxPresTrans ΓRΔ ΔRΘ w , factor2≤PresTrans ΓRΔ ΔRΘ w , R-irrel _ _)

module PresheafEvaluationIS4 = Semantics.Presheaf.Evaluation.IS4
                                 Ctx
                                 _⊆_ _∙_ (λ w w' w'' → ≡-sym (assocWk w w' w'')) idWk rightIdWk leftIdWk
                                 _R_ R-trans R-trans-assoc R-refl R-refl-unit-left R-refl-unit-right
                                 factor2 factor2-pres-id factor2-pres-∙ factor2-pres-refl factor2-pres-trans

open PresheafEvaluationIS4 renaming (module Eval to PresheafEvaluationIS4Eval; module EvalProperties to PresheafEvaluationIS4EvalProperties) public

𝒩ℯ : (a : Ty) → Psh
𝒩ℯ a = record
  { Fam           = λ Γ → Ne Γ a
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = wkNe
  ; wk-pres-≋     = λ w → cong (wkNe w)
  ; wk-pres-refl  = wkNePresId
  ; wk-pres-trans = λ w w' n → ≡-sym (wkNePres∙ w w' n)
  }

open PresheafEvaluationIS4Eval           (𝒩ℯ 𝕓) public
open PresheafEvaluationIS4EvalProperties (𝒩ℯ 𝕓) public

𝒩𝒻 : (a : Ty) → Psh
𝒩𝒻 a = record
  { Fam           = λ Γ → Nf Γ a
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = wkNf
  ; wk-pres-≋     = λ w → cong (wkNf w)
  ; wk-pres-refl  = wkNfPresId
  ; wk-pres-trans = λ w w' n → ≡-sym (wkNfPres∙ w w' n)
  }

-- renaming environments, representable presheaf, Yoneda embedding
ℛℯ𝓃 : (Γ : Ctx) → Psh
ℛℯ𝓃 Γ = record
  { Fam           = Γ ⊆_
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = λ w w' → w' ∙ w
  ; wk-pres-≋     = λ w → cong (_∙ w)
  ; wk-pres-refl  = rightIdWk
  ; wk-pres-trans = λ w w' w'' → ≡-sym (assocWk w'' w w')
  }

𝒯𝓂 : (a : Ty) → Psh
𝒯𝓂 a = record
  { Fam           = λ Γ → Tm Γ a
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = wkTm
  ; wk-pres-≋     = λ w → cong (wkTm w)
  ; wk-pres-refl  = wkTm-pres-id
  ; wk-pres-trans = λ w w' t → ≡-sym (wkTm-pres-∙ w w' t)
  }

𝒮𝓊𝒷 : (Γ : Ctx) → Psh
𝒮𝓊𝒷 Γ = record
  { Fam           = λ Δ → Sub Δ Γ
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = wkSub
  ; wk-pres-≋     = λ w → cong (wkSub w)
  ; wk-pres-refl  = wkSub-pres-id
  ; wk-pres-trans = λ w w' s → ≡-sym (wkSub-pres-∙ w w' s)
  }

-- interpretation of types
Ty' : (Γ : Ctx) → (a : Ty) → Set
Ty' Γ a = evalTy a ₀ Γ

-- interpretation of contexts ("environments")
Ctx' : (Γ : Ctx) → (Δ : Ctx) → Set
Ctx' Γ Δ = evalCtx Δ ₀ Γ

Env = Ctx'

variable
  ρ ρ' ρ'' : Env Γ Δ

-- values in the model can be weakened
wkTy' : (w : Γ ⊆ Γ') → (x : Ty' Γ a) → Ty' Γ' a
wkTy' {a = a} = wk[ evalTy a ]

-- environments in the model can be weakened
wkCtx' : (w : Γ ⊆ Γ') → (ρ : Ctx' Γ Δ) → Ctx' Γ' Δ
wkCtx' {Δ = Δ} = wk[ evalCtx Δ ]
