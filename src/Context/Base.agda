{-# OPTIONS --safe --without-K #-}
module Context.Base (Ty : Set) where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit  using (⊤ ; tt)

private
  variable
    a b c d : Ty

infixl 6 _# _`,_
infixl 5 _,,_

-----------
-- Contexts
-----------

data Ctx : Set where
  []   : Ctx
  _`,_ : (Γ : Ctx) → (a : Ty) → Ctx
  _#   : (Γ : Ctx) → Ctx            -- a lock 🔒

[#] : Ctx
[#] = [] #

[_] : Ty → Ctx
[_] a = [] `, a

variable
  Γ Γ' Γ'' ΓL ΓL' ΓL'' ΓLL ΓLR ΓR ΓR' ΓR'' ΓRL ΓRR : Ctx
  Δ Δ' Δ'' ΔL ΔL' ΔL'' ΔLL ΔLR ΔR ΔR' ΔR'' ΔRL ΔRR : Ctx
  Θ Θ' Θ'' ΘL ΘL' ΘL'' ΘLL ΘLR ΘR ΘR' ΘR'' ΘRL ΘRR : Ctx
  Ξ Ξ' Ξ'' ΞL ΞL' ΞL'' ΞLL ΞLR ΞR ΞR' ΞR'' ΞRL ΞRR : Ctx

-- append contexts (++)
_,,_ : Ctx → Ctx → Ctx
Γ ,, []       = Γ
Γ ,, (Δ `, x) = (Γ ,, Δ) `, x
Γ ,, (Δ #)    = (Γ ,, Δ) #

-- contexts free of locks
#-free : Ctx → Set
#-free []        = ⊤
#-free (Γ `, _a) = #-free Γ
#-free (_Γ #)    = ⊥

-- context to left of the last lock
←# : Ctx → Ctx
←# []        = []
←# (Γ `, _a) = ←# Γ
←# (Γ #)     = Γ

-- context to the right of the last lock
#→ : Ctx → Ctx
#→ []       = []
#→ (Γ `, a) = #→ Γ `, a
#→ (_Γ #)   = []
