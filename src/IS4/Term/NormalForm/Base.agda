{-# OPTIONS --safe --without-K #-}
module IS4.Term.NormalForm.Base where

open import IS4.Term.Base

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var   : (v : Var Γ a) → Ne Γ a
  app   : (n : Ne Γ (a ⇒ b)) → (m : Nf Γ a) → Ne Γ b
  unbox : (n : Ne ΓL (□ a)) → (e : CExt Γ ΓL ΓR) → Ne Γ a

data Nf where
  up  : (n : Ne Γ ι) → Nf Γ ι
  lam : (n : Nf (Γ `, a) b) → Nf Γ (a ⇒ b)
  box : (n : Nf (Γ #) a) → Nf Γ (□ a)

-- normal forms of substitutions (simply "do everything pointwise")
data Nfₛ : Ctx → Ctx → Set where
  []   : Nfₛ Γ []
  _`,_ : (n : Nfₛ Γ Δ) → (m : Nf Γ a) → Nfₛ Γ (Δ `, a)
  lock : (n : Nfₛ ΔL Γ) → (e : CExt Δ ΔL ΔR) → Nfₛ Δ (Γ #)

Nfₛ- : (Δ : Ctx) → (Γ : Ctx) → Set
Nfₛ- Δ Γ = Nfₛ Γ Δ

-- embedding into terms

embNe : (n : Ne Γ a) → Tm Γ a
embNf : (n : Nf Γ a) → Tm Γ a

embNe (var   v)   = var   v
embNe (app   m n) = app   (embNe m) (embNf n)
embNe (unbox n e) = unbox (embNe n) e

embNf (up  n) = embNe n
embNf (lam n) = lam (embNf n)
embNf (box n) = box (embNf n)

-- embeddding of substitution normal forms back into substitutions (simply "do everything pointwise")
embNfₛ : (N : Nfₛ Γ Δ) → Sub Γ Δ
embNfₛ []         = []
embNfₛ (n `, m)   = embNfₛ n `, embNf m
embNfₛ (lock n e) = lock (embNfₛ n) e

-- weakening lemmas

wkNe : (w : Γ ⊆ Γ') → (n : Ne Γ a) → Ne Γ' a
wkNf : (w : Γ ⊆ Γ') → (n : Nf Γ a) → Nf Γ' a

wkNe w (var   v)   = var   (wkVar w              v)
wkNe w (app   n m) = app   (wkNe  w              n) (wkNf w m)
wkNe w (unbox n e) = unbox (wkNe  (factorWk e w) n) (factorExt e w)

wkNf e (up  n) = up  (wkNe e         n)
wkNf e (lam n) = lam (wkNf (keep  e) n)
wkNf e (box n) = box (wkNf (keep# e) n)
