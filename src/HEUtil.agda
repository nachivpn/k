{-# OPTIONS --safe --with-K #-}
module HEUtil where

infixr 2 step-≅

open import Level using (Level)

open import Relation.Unary using (Pred)

open import Relation.Binary                       using (REL)
import      Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; subst ; subst₂)
  renaming (refl to ≡-refl ; trans to ≡-trans)

open HE public
  using    (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; ≡-subst-removable)
  renaming (refl to ≅-refl ; sym to ≅-sym ; trans to ≅-trans ; icong to ≅-cong)

private
  variable
    ℓ : Level
    A : Set ℓ
    B : Set ℓ

≡-subst-addable : ∀ (P : Pred A ℓ) {x y} (eq : x ≡ y) (z : P x) → z ≅ subst P eq z
≡-subst-addable P p z = ≅-sym (≡-subst-removable P p z)

-- stole it from history of master
≡-subst₂-removable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → subst₂ R eq₁ eq₂ z ≅ z
≡-subst₂-removable P ≡-refl ≡-refl z = ≅-refl

≡-subst₂-addable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → z ≅ subst₂ R eq₁ eq₂ z
≡-subst₂-addable P p q z = ≅-sym (≡-subst₂-removable P p q z)

step-≅ : ∀ (x {y z} : A) → y ≡ z → x ≅ y → x ≡ z
step-≅ _ y≡z x≅y = ≡-trans (≅-to-≡ x≅y) y≡z

syntax step-≅ x y≡z x≡y = x ≅⟨ x≡y ⟩ y≡z

-- Custom combinator to prove syntactic lemmas about unbox, lock, etc.
module _
  {C : Set}
  (T : C → Set)                             -- Type of indexed sets (terms, etc.)
  (E : C → C → Set)                         -- Type of context extensions
  {R : {ΓL ΓR : C} → T ΓL → E ΓL ΓR → Set}  -- ... (unbox, lock, etc.)
  where

  xcong : {i1 i2 j1 j2 : C} →
           i1 ≡ i2 → j1 ≡ j2 →
          {t1 : T i1} {t2 : T i2} {e1 : E i1 j1} {e2 : E i2 j2}
          (unb : {i j : C} → (t : T i ) (e : E i j) → R t e) →
          t1 ≅ t2 →
          e1 ≅ e2 →
          unb t1 e1 ≅ unb t2 e2
  xcong ≡-refl ≡-refl _ ≅-refl ≅-refl = ≅-refl
