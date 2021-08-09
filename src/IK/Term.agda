module IK.Term where

--
-- Implementation of the IK (Intuitionistic K) calculus from
-- "Fitch-Style Modal Lambda Calculi" by Ranald Clouston (2018)
--

open import IK.Type public
open import Context (Ty) public

------------------------------------
-- Variables, terms and substituions
------------------------------------

data Tm : Ctx → Ty → Set where

  var  : Var Γ a
       ---------
       → Tm Γ a

  lam  : Tm (Γ `, a) b
         -------------
       → Tm Γ (a ⇒ b)

  app  : Tm Γ (a ⇒ b) → Tm Γ a
         ---------------------
       → Tm Γ b

  box   : Tm (Γ 🔒) a
        ------------
        → Tm Γ (◻ a)

  unbox : Tm ΓL (◻ a) → LFExt Γ (ΓL 🔒) ΓR
        -------------------------
        → Tm Γ a

wkTm : Γ' ≤ Γ → Tm Γ a → Tm Γ' a
wkTm w (var x)                = var (wkVar w x)
wkTm w (lam t)                = lam (wkTm (keep w) t)
wkTm w (app t u)              = app (wkTm w t) (wkTm w u)
wkTm w (box t)                = box (wkTm (keep🔒 w) t)
wkTm w (unbox t e)            = unbox (wkTm (sliceLeft e w) t) (wkLFExt e w)

open import Substitution Ty Tm var wkTm public

-- apply substitution to a term
substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s (var x)     = substVar s x
substTm s (lam t)     = lam (substTm (wkSub fresh s `, var ze) t)
substTm s (app t u)   = app (substTm s t) (substTm s u)
substTm s (box t)     = box (substTm (lock s nil) t)
substTm (s `, _) (unbox t (ext e)) = substTm s (unbox t e)
substTm (lock s x) (unbox t nil) = unbox (substTm s t) x

-- substitution composition
_∙ₛ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
[]             ∙ₛ s'    = []
(s `, t)       ∙ₛ s'    = (s ∙ₛ s') `, substTm s' t
lock s (ext e) ∙ₛ (s' `, x) = lock s e ∙ₛ s'
lock s nil     ∙ₛ lock s' x = lock (s ∙ₛ s') x
