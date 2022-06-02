{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Context

module IK.Term.Substitution.Properties
  (Ty           : Set)
  (Ty-Decidable : Decidable (_≡_ {A = Ty}))
  (open Context Ty Ty-Decidable using (Ctx ; Var ; _⊆_))
  (Tm           : Ctx → Ty → Set)
  (var          : ∀ {Γ a} → Var Γ a → Tm Γ a)
  (wkTm         : ∀ {Γ' Γ a} → Γ ⊆ Γ' → Tm Γ a → Tm Γ' a)
  where

open import Relation.Binary.PropositionalEquality

open Context Ty Ty-Decidable hiding (Ctx ; Var ; _⊆_)

open import IK.Term.Substitution.Base Ty Ty-Decidable Tm var wkTm

private
  variable
    a b c d : Ty

--------------------
-- Substitution laws
--------------------

-- NOTE: these are only the laws that follow directly from the structure of substitutions
coh-trimSub-wkVar : (x : Var Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substVar (trimSub w s) x ≡ substVar s (wkVar w x)
coh-trimSub-wkVar ze (s `, x) (drop w)
  = coh-trimSub-wkVar ze s w
coh-trimSub-wkVar ze (s `, x) (keep w)
  = refl
coh-trimSub-wkVar (su x) (s `, x₁) (drop w)
  = coh-trimSub-wkVar (su x) s w
coh-trimSub-wkVar (su x) (s `, x₁) (keep w)
  = coh-trimSub-wkVar x s w

-- `trimSub` preserves the identity
trimSubPresId : (s : Sub Δ Γ) → trimSub idWk s ≡ s
trimSubPresId []         = refl
trimSubPresId (s `, x)   = cong (_`, _) (trimSubPresId s)
trimSubPresId (lock s x) = cong₂ lock (trimSubPresId s) refl

-- naturality of substVar
nat-substVar : (x : Var Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substVar (wkSub w s) x ≡ wkTm w (substVar s x)
nat-substVar ze     (s `, t) w = refl
nat-substVar (su x) (s `, t) w = nat-substVar x s w

-- naturality of trimSub
nat-trimSub : (s : Sub Γ Δ) (w : Δ' ⊆ Δ) (w' : Γ ⊆ Γ')
  → wkSub w' (trimSub w s) ≡ trimSub w (wkSub w' s)
nat-trimSub []         base      w' = refl
nat-trimSub (s `, t)   (drop w)  w' = nat-trimSub s w w'
nat-trimSub (s `, t)   (keep w)  w' = cong (_`, wkTm w' t) (nat-trimSub s w w')
nat-trimSub (lock s x) (keep🔒 w) w' = cong₂ lock (nat-trimSub s w _) refl

-- `trimSub` on the identity substitution embeds the weakening
trimSubId : (w : Γ ⊆ Δ) → trimSub w idₛ ≡ embWk w
trimSubId base = refl
trimSubId (drop w) = trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w))
trimSubId (keep w) = cong (_`, var ze) (trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w)))
trimSubId (keep🔒 w) = cong₂ lock (trimSubId w) refl
