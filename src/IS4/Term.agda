module IS4.Term where

--
-- Implementation of the IS4 (Intuitionistic S4) calculus from
-- "Fitch-Style Modal Lambda Calculi" by Ranald Clouston (2018)
--

open import IK.Type public
open import Context (Ty) hiding (ext🔒) public

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

  unbox : Tm ΓL (◻ a) → CExt Γ ΓL ΓR
        ----------------------------
        → Tm Γ a

wkTm : Γ' ≤ Γ → Tm Γ a → Tm Γ' a
wkTm w (var x)     = var (wkVar w x)
wkTm w (lam t)     = lam (wkTm (keep w) t)
wkTm w (app t u)   = app (wkTm w t) (wkTm w u)
wkTm w (box t)     = box (wkTm (keep🔒 w) t)
wkTm w (unbox t e) = unbox (wkTm (factor2≤ e w) t) (factor2Ext e w)

open import IS4.Substitution Ty Tm var wkTm public

-- apply substitution to a term
substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s                                (var x)
  = substVar s x
substTm s                                (lam t)
  = lam (substTm (wkSub fresh s `, var ze) t)
substTm s                                (app t u)
  = app (substTm s t) (substTm s u)
substTm s                                (box t)
  = box (substTm (lock s (ext🔒- nil)) t)
substTm s                                (unbox t nil)
  = unbox (substTm s t) nil
substTm (s `, _)                         (unbox t (ext e))
  = substTm s (unbox t e)
substTm (lock s nil)                     (unbox t (ext🔒- e))
  = substTm s (unbox t e)
substTm (lock s (ext e'))                (unbox t (ext🔒- e))
  = wkTm fresh (substTm (lock s e') (unbox t (ext🔒- e)))
substTm (lock s (ext🔒- e'))             (unbox t (ext🔒- nil))
  = unbox (substTm s t) (ext🔒- e')
substTm (lock (s `, _) (ext🔒- e'))      (unbox t (ext🔒- (ext e)))
  = substTm (lock s (ext🔒- e')) (unbox t (ext🔒- e))
substTm (lock (lock s e'') (ext🔒- e')) (unbox t (ext🔒- (ext🔒- e)))
  = substTm (lock s (ext🔒- (extRAssoc e'' e'))) (unbox t (ext🔒- e))

-- substitution composition
_∙ₛ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
[]                          ∙ₛ s'
  = []
(s `, t)                    ∙ₛ s'
  = (s ∙ₛ s') `, substTm s' t
lock s nil                  ∙ₛ s'
  = lock (s ∙ₛ s') nil
lock s (ext e)              ∙ₛ (s' `, _)
  = lock s e ∙ₛ s'
lock s (ext🔒- nil)        ∙ₛ lock s' e'
  = lock (s ∙ₛ s') e'
lock s (ext🔒- (ext e))    ∙ₛ lock (s' `, _) e'
  = lock s (ext🔒- e) ∙ₛ lock s' e'
lock s (ext🔒- (ext🔒- e)) ∙ₛ lock (lock s' e'') e'
  = lock s (ext🔒- e) ∙ₛ lock s' (extRAssoc e'' e')
