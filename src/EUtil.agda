{-# OPTIONS --safe --without-K #-}
module EUtil where

open import Data.Empty using (⊥-elim)

open import Relation.Nullary using (¬_)

contradiction : ∀ {A B : Set} → (a : A) → (¬a : ¬ A) → B
contradiction a ¬a = ⊥-elim (¬a a)
