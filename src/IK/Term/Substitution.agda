{-# OPTIONS --safe --with-K #-}
open import Context
  using    ()
  renaming (Ctx to ICtx ; _⊆_ to I⊆ ; Var to IVar)

module IK.Term.Substitution
  (Ty   : Set)
  (Tm   : ICtx Ty → Ty → Set)
  (var  : ∀ {Γ a} → IVar Ty Γ a → Tm Γ a)
  (wkTm : ∀ {Γ' Γ a} → I⊆ Ty Γ Γ' → Tm Γ a → Tm Γ' a)
  where

open import IK.Term.Substitution.Base       Ty Tm var wkTm public
open import IK.Term.Substitution.Properties Ty Tm var wkTm public
