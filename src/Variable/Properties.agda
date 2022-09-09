{-# OPTIONS --safe --without-K #-}
module Variable.Properties (Ty : Set) where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import Context.Base  Ty
open import Variable.Base Ty

private
  variable
    a b c d : Ty

wkVarPresId : (x : Var Γ a) → wkVar idWk x ≡ x
wkVarPresId zero     = refl
wkVarPresId (succ x) = cong succ (wkVarPresId x)

-- weakening a variable index increments
wkIncr : (x : Var Γ a) → wkVar fresh[ b ] x ≡ succ x
wkIncr zero     = refl
wkIncr (succ x) = cong succ (cong succ (wkVarPresId x))

-- weakening of variables (a functor map) preserves weakening composition
wkVarPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (x : Var Γ a)
  → wkVar w' (wkVar w x) ≡ wkVar (w ∙ w') x
wkVarPres∙ (drop w) (drop w') zero     = cong succ (wkVarPres∙ (drop w) w' zero)
wkVarPres∙ (drop w) (keep w') zero     = cong succ (wkVarPres∙ w w' zero)
wkVarPres∙ (keep w) (drop w') zero     = cong succ (wkVarPres∙ (keep w) w' zero)
wkVarPres∙ (keep w) (keep w') zero     = refl
wkVarPres∙ (drop w) (drop w') (succ x) = cong succ (wkVarPres∙ (drop w) w' (succ x))
wkVarPres∙ (drop w) (keep w') (succ x) = cong succ (wkVarPres∙ w w' (succ x))
wkVarPres∙ (keep w) (drop w') (succ x) = cong succ (wkVarPres∙ (keep w) w' (succ x))
wkVarPres∙ (keep w) (keep w') (succ x) = cong succ (wkVarPres∙ w w' x)
