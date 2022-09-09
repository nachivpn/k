{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module ContextExtension (Ty : Set) (Ty-Decidable : Decidable (_≡_ {A = Ty})) where

open import ContextExtension.Base       Ty              public
open import ContextExtension.Properties Ty Ty-Decidable public
