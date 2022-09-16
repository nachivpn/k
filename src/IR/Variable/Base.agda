{-# OPTIONS --safe --without-K #-}
module IR.Variable.Base (Ty : Set) where

open import Context.Base             Ty
open import IR.ContextExtension.Base Ty

private
  variable
    a b c d : Ty

data Var : (Γ : Ctx) → (a : Ty) → Set where
  zero    : Var (Γ `, a) a
  succ[_] : (b : Ty) → (v : Var Γ a) → Var (Γ `, b) a
  succ#   : (v : Var Γ a) → Var (Γ #) a -- ε ; v

pattern succ {b} v = succ[ b ] v

variable
  v v' v'' : Var Γ a

-- R structure for variables
extVar : (e : Ext Γ Δ) → (v : Var Γ a) → Var Δ a
extVar new[ Γ ]     v = succ# v
extVar (ext[ a ] e) v = succ  (extVar e v)
extVar (ext#-    e) v = succ# (extVar e v)
-- /R structure for variables
