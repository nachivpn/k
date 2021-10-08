module IS4.Term.Base where

open import Data.Product using (∃; _×_; _,_; -,_; proj₁; proj₂)

open import IK.Type public

open import Context Ty public using (Var)
open import Context Ty public hiding (Var; ext🔒)

--------
-- Terms
--------

data Tm : Ctx → Ty → Set where

  var  : (v : Var Γ a)
       ---------------
       → Tm Γ a

  lam  : (t : Tm (Γ `, a) b)
         -------------------
       → Tm Γ (a ⇒ b)

  app  : (t : Tm Γ (a ⇒ b))
       → (u : Tm Γ a)
         ------------------
       → Tm Γ b

  box   : (t : Tm (Γ 🔒) a)
        ------------------
        → Tm Γ (◻ a)

  unbox : (t : Tm ΓL (◻ a))
        → (e : CExt Γ ΓL ΓR)
        --------------------
        → Tm Γ a

variable
  t t' t'' : Tm Γ a
  u u' u'' : Tm Γ a

-- weaken a term
wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)     = var (wkVar w x)
wkTm w (lam t)     = lam (wkTm (keep w) t)
wkTm w (app t u)   = app (wkTm w t) (wkTm w u)
wkTm w (box t)     = box (wkTm (keep🔒 w) t)
wkTm w (unbox t e) = unbox (wkTm (factor2≤ e w) t) (factor2Ext e w)

-- "drop" the last variable in the context
dropₜ : Tm Γ b → Tm (Γ `, a) b
dropₜ = wkTm fresh

-- extension that "generates a new context frame"
new : CExt (Γ 🔒) Γ ([] 🔒) -- Γ R Γ 🔒
new = ext🔒- nil

new[_] = λ Γ → new {Γ}

open Substitution Tm var wkTm CExt new f2LCtx factor2≤ f2RCtx factor2Ext public
  renaming (module Composition to SubstitutionComposition)

factor2 : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → ∃ λ ΔL → ∃ λ ΔR → Sub ΔL ΓL × CExt Δ ΔL ΔR
factor2 nil        s           = -, -, s , nil
factor2 (ext e)    (s `, t)    = factor2 e s
factor2 (ext🔒- e) (lock s e')  = let (ΔL , ΔR , s' , e'') = factor2 e s in -, -, s' , extRAssoc e'' e'

f2LCtxₛ : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Ctx
f2LCtxₛ = λ e s → factor2 e s .proj₁

f2RCtxₛ : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Ctx
f2RCtxₛ = λ e s → factor2 e s .proj₂ .proj₁

factor2Sub : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Sub (f2LCtxₛ e s) ΓL
factor2Sub = λ e s → factor2 e s .proj₂ .proj₂ .proj₁

factor2Extₛ : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → CExt Δ (f2LCtxₛ e s) _
factor2Extₛ = λ e s → factor2 e s .proj₂ .proj₂ .proj₂

-- apply substitution to a term
substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s (var x)     = substVar s x
substTm s (lam t)     = lam (substTm (keepₛ s) t)
substTm s (app t u)   = app (substTm s t) (substTm s u)
substTm s (box t)     = box (substTm (keep🔒ₛ s) t)
substTm s (unbox t e) = unbox (substTm (factor2Sub e s) t) (factor2Extₛ e s)

open SubstitutionComposition substTm f2LCtxₛ factor2Sub f2RCtxₛ factor2Extₛ public

----------------
-- Derived terms
----------------

🔒-η : Sub Γ (Γ 🔒)
🔒-η = lock idₛ nil

🔒-μ : Sub (Γ 🔒 🔒) (Γ 🔒)
🔒-μ = lock idₛ (ext🔒- (ext🔒- nil))

λ′ : Tm Γ (◻ a) → Tm (Γ 🔒) a
λ′ t = unbox t new

◻-ε : Tm Γ (◻ a) → Tm Γ a
◻-ε t = substTm 🔒-η (λ′ t)

◻-δ : Tm Γ (◻ a) → Tm Γ (◻ ◻ a)
◻-δ t = box (box (substTm 🔒-μ (λ′ t)))
