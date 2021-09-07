module IS4.Conversion where

open import IS4.Term
open import IS4.Reduction

open import Data.Sum

open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to trans)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂)

open Star
open _≡_

-- Convertibility is defined taking the
-- equivalence closure of the reduction relation.
_≈_  : Tm Γ a → Tm Γ a → Set
_≈_   = EqClosure _⟶_

refl-≈ : {t : Tm Γ a} → t ≈ t
refl-≈ = ε

sym-≈ : {t t' : Tm Γ a} → t ≈ t' → t' ≈ t
sym-≈ = symmetric _⟶_

trans-≈ : {t t' u : Tm Γ a} → t ≈ t' → t' ≈ u → t ≈ u
trans-≈ = transitive _⟶_

≡-to-≈ : {t t' : Tm Γ b} → t ≡ t' → t ≈ t'
≡-to-≈ refl = ε

⟶-to-≈ : {t t' : Tm Γ b} → t ⟶ t' → t ≈ t'
⟶-to-≈ p = inj₁ p ◅ ε

⟶*-to-≈ : {t t' : Tm Γ b} → t ⟶* t' → t ≈ t'
⟶*-to-≈ ε       = ε
⟶*-to-≈ (x ◅ p) = inj₁ x ◅ ⟶*-to-≈ p
