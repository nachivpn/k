{-# OPTIONS --safe --without-K #-}
module RUtil {a} {A : Set a} {r} (R : A → A → Set r) where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

private
  variable
    x x' y y' z z' : A

≡-step-≡ : (x'≡x : x' ≡ x) → (xRy : R x y) → (y≡y' : y ≡ y') → R x' y'
≡-step-≡ refl xRy refl = xRy

step-≡ : (xRy : R x y) → (y≡y' : y ≡ y') → R x y'
step-≡ xRy refl = xRy

≡-step : (x'≡x : x' ≡ x) → (xRy : R x y) → R x' y
≡-step refl xRy = xRy
