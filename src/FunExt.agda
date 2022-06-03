{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_)
module FunExt where

postulate
  funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
           → ((x : A) → f x ≡ g x) → f ≡ g

  funexti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
           → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g
