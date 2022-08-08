{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Context (Ty : Set) (Ty-Decidable : Decidable (_≡_ {A = Ty})) where

open import Context.Base       Ty              public
open import Context.Properties Ty Ty-Decidable public
