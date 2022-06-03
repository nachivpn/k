{-# OPTIONS --without-K #-}
module FunExt where

open import Level renaming (zero to ℓ0)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Axiom.Extensionality.Propositional

postulate
  funext  : Extensionality ℓ0 ℓ0

funexti' : ∀ {A : Set} {B : A → Set} {f g : {x : A} → B x}
           → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g
funexti' x = implicit-extensionality funext (x _)
