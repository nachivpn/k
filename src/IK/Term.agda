module IK.Term where

--
-- Implementation of the IK (Intuitionistic K) calculus from
-- "Fitch-Style Modal Lambda Calculi" by Ranald Clouston (2018)
--

open import IK.Type    as Type    using (Ty)
import      Context Ty as Context

open Context public using (Var)
open Context public
open Type    public

infixr 20 _∙ₛ_

-------------------------------------
-- Variables, terms and substitutions
-------------------------------------

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
        → (e : LFExt Γ (ΓL 🔒) ΓR)
        -------------------------
        → Tm Γ a

variable
  t t' t'' : Tm Γ a
  u u' u'' : Tm Γ a

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)                = var (wkVar w x)
wkTm w (lam t)                = lam (wkTm (keep w) t)
wkTm w (app t u)              = app (wkTm w t) (wkTm w u)
wkTm w (box t)                = box (wkTm (keep🔒 w) t)
wkTm w (unbox t e)            = unbox (wkTm (sliceLeft e w) t) (wkLFExt e w)

open import IK.Substitution Ty Tm var wkTm public

-- apply substitution to a term
substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s (var x)     = substVar s x
substTm s (lam t)     = lam (substTm (wkSub fresh s `, var ze) t)
substTm s (app t u)   = app (substTm s t) (substTm s u)
substTm s (box t)     = box (substTm (keep🔒ₛ s) t)
substTm s (unbox t e) = unbox (substTm (factor2Sub e s) t) (factor2R e s)

-- substitution composition
_∙ₛ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
[]        ∙ₛ s = []
(s' `, t) ∙ₛ s = s' ∙ₛ s `, substTm s t
lock s' e ∙ₛ s = lock (s' ∙ₛ factor2Sub e s) (factor2R e s)
