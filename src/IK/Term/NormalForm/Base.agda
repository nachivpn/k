{-# OPTIONS --safe --without-K #-}
module IK.Term.NormalForm.Base where

open import IK.Term.Base

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var   : Var Γ a → Ne Γ a
  app   : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
  unbox : Ne ΓL (□ a) → LFExt Γ (ΓL #) ΓR → Ne Γ a

data Nf where
  up𝕓 : Ne Γ 𝕓 → Nf Γ 𝕓
  lam : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  box : Nf (Γ #) a → Nf Γ (□ a)

-- normal forms of substitutions (simply "do everything pointwise")
data Nfₛ : Ctx → Ctx → Set where
  []   : Nfₛ Γ []
  _`,_ : Nfₛ Γ Δ → Nf Γ a → Nfₛ Γ (Δ `, a)
  lock : Nfₛ ΔL Γ → LFExt Δ (ΔL #) ΔR → Nfₛ Δ (Γ #)

Nfₛ- : Ctx → Ctx → Set
Nfₛ- Δ Γ = Nfₛ Γ Δ

-- embedding into terms

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var x)     = var x
embNe (app m n)   = app (embNe m) (embNf n)
embNe (unbox n x) = unbox (embNe n) x

embNf (up𝕓 x) = embNe x
embNf (lam n) = lam (embNf n)
embNf (box n) = box (embNf n)

-- embeddding of substitution normal forms back into substitutions (simply "do everything pointwise")
embNfₛ : Nfₛ Γ Δ → Sub Γ Δ
embNfₛ []         = []
embNfₛ (n `, s)   = embNfₛ n `, embNf s
embNfₛ (lock n s) = lock (embNfₛ n) s

-- weakening lemmas

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var x)      = var (wkVar w x)
wkNe w (app m n)    = app (wkNe w m) (wkNf w n)
wkNe w (unbox n e)  = unbox (wkNe (sliceLeft e w) n) (wkLFExt e w)

wkNf e (up𝕓 x) = up𝕓 (wkNe e x)
wkNf e (lam n) = lam (wkNf (keep e) n)
wkNf e (box n) = box (wkNf (keep# e) n)
