{-# OPTIONS --safe --without-K #-}
module IS4.Norm.NbE.Model where

open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)

open import Relation.Binary
  using    (Reflexive ; Transitive ; Irrelevant)
open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; subst ; cong ; cong₂ ; cong-id ; subst-application)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

open import PUtil

open import IS4.Term as Term hiding (factorWk)

import Semantics.Presheaf.Evaluation.IS4

factor : ∀ (Γ◁Δ : Γ ◁IS4 Δ) (w : Δ ⊆ Δ') → ∃ λ Γ' → Γ ⊆ Γ' × Γ' ◁IS4 Δ'
factor (_ , Γ◁Δ) w = -, Term.factorWk Γ◁Δ w , -, factorExt Γ◁Δ w

factorWk : ∀ (Γ◁Δ : Γ ◁IS4 Δ) (w : Δ ⊆ Δ') → Γ ⊆ _
factorWk r w = factor r w .proj₂ .proj₁

factor◁ : ∀ (Γ◁Δ : Γ ◁IS4 Δ) (w : Δ ⊆ Δ') → _ ◁IS4 Δ'
factor◁ r w = factor r w .proj₂ .proj₂

private
  factor-pres-id : ∀ (Γ◁Δ : Γ ◁IS4 Δ) → factor Γ◁Δ idWk ≡ (-, idWk , Γ◁Δ)
  factor-pres-id (_ , Γ◁Δ) = Σ×-≡,≡,≡→≡ (lCtxPresId Γ◁Δ , factorWkPresId Γ◁Δ , ◁IS4-irrel _ _)

  factor-pres-∙ : ∀ (Γ◁Δ : Γ ◁IS4 Δ) (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') → factor Γ◁Δ (w ∙ w') ≡ (-, factorWk Γ◁Δ w ∙ factorWk (factor◁ Γ◁Δ w) w' , factor◁ (factor◁ Γ◁Δ w) w')
  factor-pres-∙ (_ , Γ◁Δ) w w' = Σ×-≡,≡,≡→≡ (lCtxPres∙ Γ◁Δ w w' , factorWkPres∙ Γ◁Δ w w' , ◁IS4-irrel _ _)

  factor-pres-refl : ∀ (w : Γ ⊆ Γ') → factor ◁IS4-refl w ≡ (-, w , ◁IS4-refl)
  factor-pres-refl w = Σ-≡,≡→≡ (lCtxPresRefl {θ = tt} w , ×-≡,≡→≡ (factorWkPresRefl {θ = tt} w , ◁IS4-irrel _ _))

  factor-pres-trans : ∀ (Γ◁Δ : Γ ◁IS4 Δ) (Δ◁Θ : Δ ◁IS4 Θ) (w : Θ ⊆ Θ') → factor (◁IS4-trans Γ◁Δ Δ◁Θ) w ≡ (-, factorWk Γ◁Δ (factorWk Δ◁Θ w) , ◁IS4-trans (factor◁ Γ◁Δ (factorWk Δ◁Θ w)) (factor◁ Δ◁Θ w))
  factor-pres-trans (_ , Γ◁Δ) (_ , Δ◁Θ) w = Σ×-≡,≡,≡→≡ (lCtxPresTrans Γ◁Δ Δ◁Θ w , factorWkPresTrans Γ◁Δ Δ◁Θ w , ◁IS4-irrel _ _)

module PresheafEvaluationIS4 = Semantics.Presheaf.Evaluation.IS4
                                 Ctx
                                 _⊆_ _∙_ (λ w w' w'' → ≡-sym (assocWk w w' w'')) idWk rightIdWk leftIdWk
                                 _◁IS4_ ◁IS4-trans ◁IS4-trans-assoc ◁IS4-refl ◁IS4-refl-unit-left ◁IS4-refl-unit-right
                                 factor factor-pres-id factor-pres-∙ factor-pres-refl factor-pres-trans

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

open PresheafEvaluationIS4Eval (𝒩ℯ ι)           public
  hiding (Sub' ; Tm')
open PresheafEvaluationIS4EvalProperties (𝒩ℯ ι) public

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
Tm' : (Γ : Ctx) → (a : Ty) → Set
Tm' Γ a = evalTy a ₀ Γ

Tm'- : Ty → Ctx → Set
Tm'- a Γ = Tm' Γ a

-- interpretation of contexts ("environments")
Sub' : (Γ : Ctx) → (Δ : Ctx) → Set
Sub' Γ Δ = evalCtx Δ ₀ Γ

Sub'- : Ctx → Ctx → Set
Sub'- Δ Γ = Sub' Γ Δ

variable
  ρ ρ' ρ'' : Sub' Γ Δ

-- values in the model can be weakened
wkTy' wkTm' : (a : Ty) → (w : Γ ⊆ Γ') → (x : Tm' Γ a) → Tm' Γ' a
wkTy' a = wk[ evalTy a ]
wkTm' = wkTy'

-- environments in the model can be weakened
wkSub' : (Δ : Ctx) → (w : Γ ⊆ Γ') → (ρ : Sub' Γ Δ) → Sub' Γ' Δ
wkSub' Δ = wk[ evalCtx Δ ]

-- semantic counterpart of `unbox` from `Tm`
unbox' : Tm' ΓL (□ a) → CExt Γ ΓL ΓR → Tm' Γ a
unbox' (elem bx _bx-nat) e = bx idWk (-, e)

unlock' : Sub' Δ (Γ #) → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → Sub' ΔL Γ × CExt Δ ΔL ΔR }
unlock' (elem (ΔL , (ΔR , e), s)) = (ΔL , ΔR) , (s , e)

-- interpretation of variables
substVar' : Var Γ a → Sub'- Γ →̇ Tm'- a
substVar' v = evalVar v .apply

CExt' : CExt Γ ΓL ΓR → Sub'- Γ →̇ Sub'- (ΓL #)
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
