{-# OPTIONS --without-K #-}
module IK.Applications.Neutrality where

open import Data.Empty using (⊥)

open import Relation.Binary using (Transitive)

open import IK.Term.Base

open import IK.Term.NormalForm.Base

infixr 3 _⊲_ _⊲ᶜ_

-- positive subformulas?
data _⊲_ : (a : Ty) → (b : Ty) → Set where
  ⊲-refl : a ⊲ a
  sbr⇒   : (a◁b : a ⊲ b) → a ⊲ c ⇒ b
  sb□    : (a◁b : a ⊲ b) → a ⊲ □ b

data _⊲ᶜ_ : (a : Ty) → (Γ : Ctx) → Set where
  here   : (a◁b : a ⊲  b) → a ⊲ᶜ Γ `, b
  there  : (a◁Γ : a ⊲ᶜ Γ) → a ⊲ᶜ Γ `, b
  there# : (a◁Γ : a ⊲ᶜ Γ) → a ⊲ᶜ Γ #

noClosedNe : (n : Ne [] a) → ⊥
noClosedNe (app n m) = noClosedNe n

neutrVar : (v : Var Γ a) → a ⊲ᶜ Γ
neutrVar zero     = here  ⊲-refl
neutrVar (succ v) = there (neutrVar v)

⊲-trans : Transitive _⊲_
⊲-trans a◁b ⊲-refl     = a◁b
⊲-trans a◁b (sbr⇒ b◁c) = sbr⇒ (⊲-trans a◁b b◁c)
⊲-trans a◁b (sb□  b◁c) = sb□  (⊲-trans a◁b b◁c)

⊲-lift : (a◁b : a ⊲ b) → (b◁Γ : b ⊲ᶜ Γ) → a ⊲ᶜ Γ
⊲-lift a◁b (here   b◁c) = here   (⊲-trans a◁b b◁c)
⊲-lift a◁b (there  b◁Γ) = there  (⊲-lift  a◁b b◁Γ)
⊲-lift a◁b (there# b◁Γ) = there# (⊲-lift  a◁b b◁Γ)

neutrality : (n : Ne Γ a) → a ⊲ᶜ Γ
neutrality (var   v)         = neutrVar v
neutrality (app   n m)       = ⊲-lift (sbr⇒ ⊲-refl) (neutrality n)
neutrality (unbox n nil)     = there# (⊲-lift (sb□ ⊲-refl) (neutrality n))
neutrality (unbox n (ext e)) = there  (neutrality (unbox n e))
