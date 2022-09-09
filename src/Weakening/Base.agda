{-# OPTIONS --safe --without-K #-}
module Weakening.Base (Ty : Set) where

open import Context.Base Ty

infix 5 _⊆_

private
  variable
    a b c d : Ty

-- weakening relation
data _⊆_  : Ctx → Ctx → Set where
  base   : [] ⊆ []
  drop   : (w : Γ ⊆ Δ) → Γ ⊆ Δ `, a
  keep   : (w : Γ ⊆ Δ) → Γ `, a ⊆ Δ `, a
  keep#  : (w : Γ ⊆ Δ) → Γ # ⊆ Δ #

{-
  Notes on _⊆_:

  In addition to the regular definition of weakening (`base`, `drop` and `keep`),
  we also allow weakening in the presence of locks:

  - `keep#` allows weakening under locks

  Disallowing weakening with locks in general ensures that values
  that depend on "local" assumptions cannot be boxed by simply
  weakening with locks.

-}

pattern drop[_] a w = drop {a = a} w
pattern keep[_] a w = keep {a = a} w

variable
  w w' w'' : Γ ⊆ Γ'

-- weakening is reflexive
idWk[_] : (Γ : Ctx) → Γ ⊆ Γ
idWk[_] []        = base
idWk[_] (Γ `, _a) = keep  idWk[ Γ ]
idWk[_] (Γ #)     = keep# idWk[ Γ ]

idWk = λ {Γ} → idWk[ Γ ]

-- weakening is transitive (or can be composed)
_∙_ : Θ ⊆ Δ → Δ ⊆ Γ → Θ ⊆ Γ
w       ∙ base     = w
w       ∙ drop  w' = drop  (w ∙ w')
drop  w ∙ keep  w' = drop  (w ∙ w')
keep  w ∙ keep  w' = keep  (w ∙ w')
keep# w ∙ keep# w' = keep# (w ∙ w')

-- weakening that "generates a fresh variable"
fresh : Γ ⊆ Γ `, a
fresh = drop idWk

fresh[_] = λ {Γ} a → fresh {Γ} {a}
