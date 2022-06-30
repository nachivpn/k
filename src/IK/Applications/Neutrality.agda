{-# OPTIONS --without-K #-}
module IK.Applications.Neutrality where

open import Data.Empty

open import Relation.Binary using (Transitive)

open import IK.Norm.Base
open import IK.Term

infixr 3 _⊲_
infixr 3 _⊲ᶜ_

-- positive subformulas?
data _⊲_ : Ty → Ty → Set where
    ⊲-refl  : a ⊲ a
    sbr⇒    : a ⊲ c → a ⊲ (b ⇒ c)
    sb□    : a ⊲ b → a ⊲ □ b

data _⊲ᶜ_   : (a : Ty) → (Γ : Ctx) → Set where
  here    :  a ⊲ b  → a ⊲ᶜ (Γ `, b)
  there   :  a ⊲ᶜ Γ → a ⊲ᶜ (Γ `, b)
  there#  :  a ⊲ᶜ Γ → a ⊲ᶜ Γ #

noClosedNe : Ne [] a → ⊥
noClosedNe (app n x) = noClosedNe n

neutrVar : Var Γ a → a ⊲ᶜ Γ
neutrVar ze     = here ⊲-refl
neutrVar (su x) = there (neutrVar x)

⊲-trans : Transitive _⊲_
⊲-trans x ⊲-refl   = x
⊲-trans x (sbr⇒ y) = sbr⇒ (⊲-trans x y)
⊲-trans x (sb□ y) = sb□ (⊲-trans x y)

⊲-lift : a ⊲ b → b ⊲ᶜ Γ → a ⊲ᶜ Γ
⊲-lift p (here x)   = here (⊲-trans p x)
⊲-lift p (there q)  = there (⊲-lift p q)
⊲-lift p (there# q) = there# (⊲-lift p q)

neutrality : Ne Γ a → a ⊲ᶜ Γ
neutrality (var x)           = neutrVar x
neutrality (app n x)         = ⊲-lift (sbr⇒ ⊲-refl) (neutrality n)
neutrality (unbox n nil)     = there# (⊲-lift (sb□ ⊲-refl) (neutrality n))
neutrality (unbox n (ext e)) = there (neutrality (unbox n e))
