{-# OPTIONS --safe --without-K #-}
module PEUtil where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; subst ; subst₂)

module _ {a} {A : Set a} {x y z : A} where
  trans˘ : x ≡ y → z ≡ y → x ≡ z
  trans˘ x≡y z≡y = trans x≡y (sym z≡y)

  ˘trans : y ≡ x → y ≡ z → x ≡ z
  ˘trans y≡x y≡z = trans (sym y≡x) y≡z

module _ {a} {A : Set a} {b} {B : Set b} {x y : A} where
  cong˘ : (f : A → B) → y ≡ x → f x ≡ f y
  cong˘ f y≡x = cong f (sym y≡x)

module _ {a} {A : Set a} {b} where
  subst˘ : (B : A → Set b) {x y : A} → y ≡ x → B x → B y
  subst˘ B y≡x b = subst B (sym y≡x) b

module _ {a} {b} {c} where
  cong1 : ∀ {A : Set a} {B : Set b} {C : Set c}
           (f : A → B → C) {x₁ x₂ y}
         → (p : x₁ ≡ x₂)
         → f x₁ y ≡ f x₂ y
  cong1 _f refl = refl

module _ {a} {b} {c} where
  cong2 : ∀ {A : Set a} {B : Set b} {C : Set c}
           (f : A → B → C) {x y₁ y₂}
         → (p : y₁ ≡ y₂)
         → f x y₁ ≡ f x y₂
  cong2 _f refl = refl

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

module _ {a} {b} {c} {d} {e} where
  idcong₄ : ∀ {A : Set a} {B : Set b} {C : A → Set c} {D : A → B → Set d} {E : Set e}
            (f : {x : A} → {y : B} → C x → D x y → E) {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂}
          → (p : w₁ ≡ w₂) → (q : x₁ ≡ x₂) → subst C p y₁ ≡ y₂ → subst₂ D p q z₁ ≡ z₂
          → f {w₁} {x₁} y₁ z₁ ≡ f {w₂} {x₂} y₂ z₂
  idcong₄ _f refl refl refl refl = refl

subst-application′ : ∀ {a b₁ b₂} {A : Set a}
                    (B₁ : A → Set b₁) {B₂ : A → Set b₂}
                    {x₁ x₂ : A} {y : B₁ x₁}
                    (g : {x : A} → B₁ x → B₂ x)
                    (eq : x₁ ≡ x₂) →
                    subst B₂ eq (g y) ≡ g (subst B₁ eq y)
subst-application′ _ _ refl = refl

open import Relation.Binary.Definitions using (Decidable)

module Decidable⇒K {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) where
  open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

  open Decidable⇒UIP _≟_ public

  K : {a : A} → (p : a ≡ a) → p ≡ refl
  K p = ≡-irrelevant p refl
