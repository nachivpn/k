{-# OPTIONS --safe --with-K #-}
module IK.Type where

infixr 7 _⇒_

data Ty : Set where
  𝕓   : Ty
  _⇒_ : (a : Ty) → (b : Ty) → Ty
  ◻_  : (a : Ty) → Ty

variable
    a b c d : Ty
