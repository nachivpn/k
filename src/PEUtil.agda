{-# OPTIONS --safe --without-K #-}
module PEUtil where

open import Relation.Binary.Definitions
  using (Decidable)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; subst ; subst₂)

≡[]-syntax = _≡_ ; syntax ≡[]-syntax {A = A} a b = a ≡[ A ] b

module _ {a} {A : Set a} {x y z : A} where
  trans˘ : x ≡ y → z ≡ y → x ≡ z
  trans˘ x≡y z≡y = trans x≡y (sym z≡y)

  ˘trans : y ≡ x → y ≡ z → x ≡ z
  ˘trans y≡x y≡z = trans (sym y≡x) y≡z

module _ {a} {A : Set a} {b} {B : Set b} {x y : A} where
  cong˘ : (f : A → B) → y ≡ x → f x ≡ f y
  cong˘ f y≡x = cong f (sym y≡x)

module _ {a} {b} {c} where
  cong1 : ∀ {A : Set a} {B : Set b} {C : Set c}
            (f : A → B → C) {x₁ x₂ y}
        → (p : x₁ ≡ x₂)
        → f x₁ y ≡ f x₂ y
  cong1 _f refl = refl

  cong1˘ : ∀ {A : Set a} {B : Set b} {C : Set c}
             (f : A → B → C) {x₁ x₂ y}
         → (p : x₂ ≡ x₁)
         → f x₁ y ≡ f x₂ y
  cong1˘ _f refl = refl

module _ {a} {b} {c} where
  cong2 : ∀ {A : Set a} {B : Set b} {C : Set c}
            (f : A → B → C) {x y₁ y₂}
        → (p : y₁ ≡ y₂)
        → f x y₁ ≡ f x y₂
  cong2 _f refl = refl

module _ {a} {A : Set a} {p} (P : A → Set p) where
  subst˘ : ∀ {x₁ x₂} → x₂ ≡ x₁ → P x₁ → P x₂
  subst˘ x₂≡x₁ = subst P (sym x₂≡x₁)

module _ {a} {A : Set a} {b} {B : Set b} {r} (R : A → B → Set r) where
  subst1 : ∀ {x₁ x₂ y} → x₁ ≡ x₂ → R x₁ y → R x₂ y
  subst1 {_x₁} {_x₂} {y} = subst (λ x → R x y)

  subst1˘ : ∀ {x₁ x₂ y} → x₂ ≡ x₁ → R x₁ y → R x₂ y
  subst1˘ x₂≡x₁ = subst1 (sym x₂≡x₁)

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

module _ {a} {b} {c} {d} {e} where
  dcong₄ : ∀ {A : Set a} {B : A → Set b} {C : A → Set c} {D : A → Set d} {E : Set e}
           (f : (w : A) → B w → C w → D w → E) {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂}
         → (p : w₁ ≡ w₂) → subst B p x₁ ≡ x₂ → subst C p y₁ ≡ y₂ → subst D p z₁ ≡ z₂
         → f w₁ x₁ y₁ z₁ ≡ f w₂ x₂ y₂ z₂
  dcong₄ _f refl refl refl refl = refl

subst-sym : ∀ {a p} {A : Set a} {P : A → Set p}
            {x₁ x₂ : A} {y₁ : P x₁} {y₂ : P x₂}
            (eq : x₁ ≡ x₂)
          → subst P eq y₁ ≡ y₂
          → y₁ ≡ subst P (sym eq) y₂
subst-sym refl y₁≡y₂ = y₁≡y₂

module _ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
         (g : {x : A} → P x → Q x) where
  subst-application′ : ∀ {x₁ x₂ y} → (eq : x₁ ≡ x₂)
                     → subst Q eq (g y) ≡ g (subst P eq y)
  subst-application′ refl = refl

  subst˘-application′ : ∀ {x₁ x₂ y} → (eq : x₂ ≡ x₁)
                      → subst˘ Q eq (g y) ≡ g (subst˘ P eq y)
  subst˘-application′ refl = refl

module _ {a p} {A : Set a} {P : A → Set p}
         (g : {x : A} → P x) where
  subst-application′′ : ∀ {x₁ x₂} → (eq : x₁ ≡ x₂)
                      → subst P eq g ≡ g
  subst-application′′ refl = refl

module _ {a p b q} {A : Set a} {P : A → Set p} {B : Set b} {Q : A → Set q}
         (g : {x : A} → P x → B → Q x) where
  subst-application1′ : ∀ {x₁ x₂ y z} → (eq : x₁ ≡ x₂)
                      → subst Q eq (g y z) ≡ g (subst P eq y) z
  subst-application1′ refl = refl

  subst˘-application1′ : ∀ {x₁ x₂ y z} → (eq : x₂ ≡ x₁)
                       → subst˘ Q eq (g y z) ≡ g (subst˘ P eq y) z
  subst˘-application1′ refl = refl

module _ {a} (A : Set a) where
  K : Set a
  K = {a : A} → (p : a ≡ a) → p ≡ refl

module Decidable⇒K {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) where
  open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

  open Decidable⇒UIP _≟_ public
    using    ()
    renaming (≡-irrelevant to Decidable⇒UIP)

  Decidable⇒K : K A
  Decidable⇒K p = Decidable⇒UIP p refl
