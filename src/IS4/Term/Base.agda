{-# OPTIONS --safe --without-K #-}
module IS4.Term.Base where

--
-- Implementation of the IS4 (Intuitionistic S4) calculus from
-- "Fitch-Style Modal Lambda Calculi" by Ranald Clouston (2018)
--

open import Data.Product using (∃ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality using (sym ; subst)

open import IK.Type as Type using (Ty ; Ty-Decidable)

import Context Ty Ty-Decidable as Context

open Context public hiding (ext🔒)
open Type    public

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
        → Tm Γ (□ a)

  unbox : (t : Tm ΓL (□ a))
        → (e : CExt Γ ΓL ΓR)
        --------------------
        → Tm Γ a

variable
  t t' t'' : Tm Γ a
  u u' u'' : Tm Γ a

pattern var0 = var v0
pattern var1 = var v1
pattern var2 = var v2

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)     = var (wkVar w x)
wkTm w (lam t)     = lam (wkTm (keep w) t)
wkTm w (app t u)   = app (wkTm w t) (wkTm w u)
wkTm w (box t)     = box (wkTm (keep🔒 w) t)
wkTm w (unbox t e) = unbox (wkTm (factorWk e w) t) (factorExt e w)

-- extension that "generates a new context frame"
new : CExt (Γ 🔒) Γ ([] 🔒) -- Γ R Γ 🔒
new = ext🔒- nil

new[_] = λ Γ → new {Γ}

open Substitution Tm var wkTm CExt new lCtx factorWk rCtx factorExt public
  renaming (module Composition to SubstitutionComposition)

-- "Left" context of factoring with a substitution (see factorSubₛ and factorExtₛ)
lCtxₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Ctx
lCtxₛ {Δ = Δ} nil       s           = Δ
lCtxₛ         (ext e)   (s `, t)    = lCtxₛ e s
lCtxₛ         (ext🔒- e) (lock s e') = lCtxₛ e s

factorSubₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Sub (lCtxₛ e s) ΓL
factorSubₛ nil       s           = s
factorSubₛ (ext e)   (s `, t)    = factorSubₛ e s
factorSubₛ (ext🔒- e) (lock s e') = factorSubₛ e s

-- "Right" context of factoring with a substitution (see factorExtₛ)
rCtxₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Ctx
rCtxₛ nil       s                     = []
rCtxₛ (ext e)   (s `, t)              = rCtxₛ e s
rCtxₛ (ext🔒- e) (lock {ΔR = ΔR} s e') = rCtxₛ e s ,, ΔR

factorExtₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → CExt Δ (lCtxₛ e s) (rCtxₛ e s)
factorExtₛ nil       s           = nil
factorExtₛ (ext e)   (s `, _)    = factorExtₛ e s
factorExtₛ (ext🔒- e) (lock s e') = extRAssoc (factorExtₛ e s) e'

-- apply substitution to a term
substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s (var x)     = substVar s x
substTm s (lam t)     = lam (substTm (keepₛ s) t)
substTm s (app t u)   = app (substTm s t) (substTm s u)
substTm s (box t)     = box (substTm (keep🔒ₛ s) t)
substTm s (unbox t e) = unbox (substTm (factorSubₛ e s) t) (factorExtₛ e s)

open SubstitutionComposition substTm lCtxₛ factorSubₛ rCtxₛ factorExtₛ public
