{-# OPTIONS --safe --without-K #-}
module Type.Base where

infixr 7 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : (a : Ty) → (b : Ty) → Ty
  □_  : (a : Ty) → Ty

variable
  a b c d : Ty
