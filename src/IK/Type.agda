module IK.Type where

infixr 7 _⇒_

data Ty : Set where
  𝕓   : Ty
  _⇒_ : Ty → Ty → Ty
  ◻_  : Ty → Ty

variable
    a b c d : Ty
