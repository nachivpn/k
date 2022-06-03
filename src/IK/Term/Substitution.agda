{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Context

module IK.Term.Substitution
  (Ty           : Set)
  (Ty-Decidable : Decidable (_≡_ {A = Ty}))
  (open Context Ty Ty-Decidable using (Ctx ; Var ; _⊆_))
  (Tm           : Ctx → Ty → Set)
  (var          : ∀ {Γ a} → Var Γ a → Tm Γ a)
  (wkTm         : ∀ {Γ' Γ a} → Γ ⊆ Γ' → Tm Γ a → Tm Γ' a)
  where

open import IK.Term.Substitution.Base       Ty Ty-Decidable Tm var wkTm public
open import IK.Term.Substitution.Properties Ty Ty-Decidable Tm var wkTm public
