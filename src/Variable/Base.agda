{-# OPTIONS --safe --without-K #-}
module Variable.Base (Ty : Set) where

open import Context.Base Ty

private
  variable
    a b c d : Ty

data Var : Ctx → Ty → Set where
  zero : Var (Γ `, a) a
  succ : (v : Var Γ a) → Var (Γ `, b) a

pattern v0 = zero
pattern v1 = succ v0
pattern v2 = succ v1

wkVar : Γ ⊆ Γ' → Var Γ a → Var Γ' a
wkVar (drop e) v        = succ (wkVar e v)
wkVar (keep e) zero     = zero
wkVar (keep e) (succ v) = succ (wkVar e v)

-- OBS: in general, Γ ⊈ Δ ,, Γ
leftWkVar : (v : Var Γ a) → Var (Δ ,, Γ) a
leftWkVar zero     = zero
leftWkVar (succ v) = succ (leftWkVar v)
