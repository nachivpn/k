{-# OPTIONS --safe --without-K #-}
module PEUtil where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; subst)

module _ {a} {A : Set a} {x y z : A} where
  trans˘ : x ≡ y → z ≡ y → x ≡ z
  trans˘ x≡y z≡y = trans x≡y (sym z≡y)

  ˘trans : y ≡ x → y ≡ z → x ≡ z
  ˘trans y≡x y≡z = trans (sym y≡x) y≡z

module _ {a} {b} {c} where
  dcong₂ : ∀ {A : Set a} {B : A → Set b} {C : Set c}
           (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
         → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
         → f x₁ y₁ ≡ f x₂ y₂
  dcong₂ _f refl refl = refl

module _ {a} {b} {c} {d} where
  dcong₃ : ∀ {A : Set a} {B : A → Set b} {C : A → Set c} {D : Set d}
           (f : (x : A) → B x → C x → D) {x₁ x₂ y₁ y₂ z₁ z₂}
         → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → subst C p z₁ ≡ z₂
         → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
  dcong₃ _f refl refl refl = refl

subst-application′ : ∀ {a b₁ b₂} {A : Set a}
                    (B₁ : A → Set b₁) {B₂ : A → Set b₂}
                    {x₁ x₂ : A} {y : B₁ x₁}
                    (g : {x : A} → B₁ x → B₂ x)
                    (eq : x₁ ≡ x₂) →
                    subst B₂ eq (g y) ≡ g (subst B₁ eq y)
subst-application′ _ _ refl = refl
