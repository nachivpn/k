module HEUtil where

open import Relation.Unary using (Pred)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_)

open import Level using (Level)

infixr 2 step-≅

private
  variable
    ℓ : Level
    A : Set ℓ
    B : Set ℓ

≡-to-≅ = HE.≡-to-≅

≅-to-≡ = HE.≅-to-≡

≡-subst-removable = HE.≡-subst-removable

≡-subst-addable : ∀ (P : Pred A ℓ) {x y} (eq : x ≡ y) (z : P x) → z ≅ subst P eq z
≡-subst-addable P p z = HE.sym (≡-subst-removable P p z)

-- stole it from history of master
≡-subst₂-removable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → subst₂ R eq₁ eq₂ z ≅ z
≡-subst₂-removable P refl refl z = HE.refl

≡-subst₂-addable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → z ≅ subst₂ R eq₁ eq₂ z
≡-subst₂-addable P p q z = HE.sym (≡-subst₂-removable P p q z)

step-≅ : ∀ (x {y z} : A) → y ≡ z → x ≅ y → x ≡ z
step-≅ _ y≡z x≅y = trans (HE.≅-to-≡ x≅y) y≡z

syntax step-≅ x y≡z x≡y = x ≅⟨ x≡y ⟩ y≡z
