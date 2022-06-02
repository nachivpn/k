{-# OPTIONS --safe --with-K #-}
module IS4.Norm.NbE.Model where

open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)

open import Relation.Binary
  using    (Reflexive ; Transitive ; Irrelevant)
open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; subst ; cong ; cong₂ ; cong-id ; subst-application)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

open import PUtil

open import IS4.Term

import Semantics.Presheaf.Evaluation.IS4

_R_ = λ Γ Δ → ∃ λ Γ' → CExt Δ Γ Γ'

variable
  r r' r'' : Γ R Δ

pattern nilR      = _ , nil
pattern extR e    = _ , ext e
pattern ext🔒R e = _ , ext🔒- e
pattern newR      = _ , ext🔒- nil

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
-- factor1⊆ w r = factor1 w r .proj₂ .proj₂

-- factor1R : ∀ (w : Γ ⊆ Γ') (r : Γ' R Δ') → Γ R _
-- factor1R w r = factor1 w r .proj₂ .proj₁

factor2 : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') → ∃ λ Γ' → Γ ⊆ Γ' × Γ' R Δ'
factor2 (_ , ΓRΔ) w = -, factorWk ΓRΔ w , -, factorExt ΓRΔ w

factor2⊆ : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') → Γ ⊆ _
factor2⊆ r w = factor2 r w .proj₂ .proj₁

factor2R : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') → _ R Δ'
factor2R r w = factor2 r w .proj₂ .proj₂

private
  factor2-pres-id : ∀ (r : Γ R Δ) → factor2 r idWk ≡ (-, idWk , r)
  factor2-pres-id (_ , ΓRΔ) = Σ×-≡,≡,≡→≡ (lCtxPresId ΓRΔ , factorWkPresId ΓRΔ , R-irrel _ _)

  factor2-pres-∙ : ∀ (r : Γ R Δ) (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') → factor2 r (w ∙ w') ≡ (-, factor2⊆ r w ∙ factor2⊆ (factor2R r w) w' , factor2R (factor2R r w) w')
  factor2-pres-∙ (_ , ΓRΔ) w w' = Σ×-≡,≡,≡→≡ (lCtxPres∙ ΓRΔ w w' , factorWkPres∙ ΓRΔ w w' , R-irrel _ _)

  factor2-pres-refl : ∀ (w : Γ ⊆ Γ') → factor2 R-refl w ≡ (-, w , R-refl)
  factor2-pres-refl w = Σ-≡,≡→≡ (lCtxPresRefl {θ = tt} w , ×-≡,≡→≡ (factorWkPresRefl {θ = tt} w , R-irrel _ _))

  factor2-pres-trans : ∀ (r : Γ R Δ) (r' : Δ R Θ) (w : Θ ⊆ Θ') → factor2 (R-trans r r') w ≡ (-, factor2⊆ r (factor2⊆ r' w) , R-trans (factor2R r (factor2⊆ r' w)) (factor2R r' w))
  factor2-pres-trans (_ , ΓRΔ) (_ , ΔRΘ) w = Σ×-≡,≡,≡→≡ (lCtxPresTrans ΓRΔ ΔRΘ w , factorWkPresTrans ΓRΔ ΔRΘ w , R-irrel _ _)

module PresheafEvaluationIS4 = Semantics.Presheaf.Evaluation.IS4
                                 Ctx
                                 _⊆_ _∙_ (λ w w' w'' → ≡-sym (assocWk w w' w'')) idWk rightIdWk leftIdWk
                                 _R_ R-trans R-trans-assoc R-refl R-refl-unit-left R-refl-unit-right
                                 factor2 factor2-pres-id factor2-pres-∙ factor2-pres-refl factor2-pres-trans

open PresheafEvaluationIS4 public
  hiding   (_→̇_ ; unbox')
  renaming (module Eval to PresheafEvaluationIS4Eval ; module EvalProperties to PresheafEvaluationIS4EvalProperties)

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

open PresheafEvaluationIS4Eval (𝒩ℯ 𝕓)           public
  hiding (Sub' ; Tm')
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
  ; wk-pres-refl  = wkTmPresId
  ; wk-pres-trans = λ w w' t → ≡-sym (wkTmPres∙ w w' t)
  }

𝒮𝓊𝒷 : (Γ : Ctx) → Psh
𝒮𝓊𝒷 Γ = record
  { Fam           = λ Δ → Sub Δ Γ
  ; _≋_           = _≡_
  ; ≋-equiv       = λ _ → ≡-equiv
  ; wk            = wkSub
  ; wk-pres-≋     = λ w → cong (wkSub w)
  ; wk-pres-refl  = wkSubPresId
  ; wk-pres-trans = λ w w' s → ≡-sym (wkSubPres∙ w w' s)
  }

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

-- interpretation of types
Ty' Tm' : (Γ : Ctx) → (a : Ty) → Set
Ty' Γ a = evalTy a ₀ Γ
Tm' = Ty'

Tm'- : Ty → Ctx → Set
Tm'- a Γ = Tm' Γ a

-- interpretation of contexts ("environments")
Ctx' Sub' : (Γ : Ctx) → (Δ : Ctx) → Set
Ctx' Γ Δ = evalCtx Δ ₀ Γ
Sub' = Ctx'

Sub'- : Ctx → Ctx → Set
Sub'- Δ Γ = Sub' Γ Δ

Env = Ctx'

variable
  ρ ρ' ρ'' : Env Γ Δ

-- values in the model can be weakened
wkTy' wkTm' : (a : Ty) → (w : Γ ⊆ Γ') → (x : Ty' Γ a) → Ty' Γ' a
wkTy' a = wk[ evalTy a ]
wkTm' = wkTy'

-- environments in the model can be weakened
wkCtx' wkSub' : (Δ : Ctx) → (w : Γ ⊆ Γ') → (ρ : Ctx' Γ Δ) → Ctx' Γ' Δ
wkCtx' Δ = wk[ evalCtx Δ ]
wkSub' = wkCtx'

-- semantic counterpart of `unbox` from `Tm`
unbox' : Tm' ΓL (◻ a) → CExt Γ ΓL ΓR → Tm' Γ a
unbox' (elem bx _bx-nat) e = bx idWk (-, e)

unlock' : Sub' Δ (Γ 🔒) → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → Sub' ΔL Γ × CExt Δ ΔL ΔR }
unlock' (elem (ΔL , (ΔR , e), s)) = (ΔL , ΔR) , (s , e)

-- interpretation of variables
substVar' : Var Γ a → Sub'- Γ →̇ Tm'- a
substVar' v = evalVar v .apply

CExt' : CExt Γ ΓL ΓR → Sub'- Γ →̇ Sub'- (ΓL 🔒)
CExt' e = evalAcc e .apply

module _ (e : CExt Γ ΓL ΓR) (s : Sub' Δ Γ) (let elem (ΔL , (ΔR , e') , s') = evalAcc e .apply s) where
  -- "Left" context of factoring with a substitution (see factorExtₛ)
  lCtxₛ' : Ctx
  lCtxₛ' = ΔL

  -- "Right" context of factoring with a substitution (see factorExtₛ)
  rCtxₛ' : Ctx
  rCtxₛ' = ΔR

  -- same as factorExtₛ
  factorExtₛ' : CExt Δ lCtxₛ' rCtxₛ'
  factorExtₛ' = e'

  -- same as factorSubₛ
  factorSubₛ' : Sub' lCtxₛ' ΓL
  factorSubₛ' = s'

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval t s = evalTm t .apply s

-- interpretation of substitutions
evalₛ : Sub Γ Δ → Sub'- Γ  →̇ Sub'- Δ
evalₛ s γ = evalSub s .apply γ
