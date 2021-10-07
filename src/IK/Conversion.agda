module IK.Conversion where

open import IK.Term
open import IK.Reduction
  as Reduction

import Data.Sum as Sum

open import Relation.Nullary
  using (¬_)

open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Equivalence.Properties
  using (a—↠b⇒a↔b)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  as ReflexiveTransitive
  using (Star)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; cong₂)

open Sum public
  using (inj₁ ; inj₂)
open ReflexiveTransitive public
  using    (ε ; _◅_)
  renaming (_◅◅_ to multi)

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

⟶-to-≈ : t ⟶ t' → t ≈ t'
⟶-to-≈ p = inj₁ p ◅ ε

⟶*-to-≈ : t ⟶* t' → t ≈ t'
⟶*-to-≈ = a—↠b⇒a↔b

module _ {t : Tm Γ a → Tm Δ b} (cong-t : ∀ {u u' : Tm Γ a} → (u⟶u' : u ⟶ u') → t u ⟶ t u') where
  -- XXX: fold
  cong-⟶-to-cong-≈ : ∀ (u≈u' : u ≈ u') → t u ≈ t u'
  cong-⟶-to-cong-≈ ε                     = ε
  cong-⟶-to-cong-≈ (inj₁ u⟶u'' ◅ u''≈u') = inj₁ (cong-t u⟶u'') ◅ cong-⟶-to-cong-≈ u''≈u'
  cong-⟶-to-cong-≈ (inj₂ u⟵u'' ◅ u''≈u') = inj₂ (cong-t u⟵u'') ◅ cong-⟶-to-cong-≈ u''≈u'

red-fun≈ : (t : Tm (Γ `, a) b) (u : Tm Γ a) → (app (lam t) u) ≈ substTm (idₛ `, u) t
red-fun≈ t u = ⟶-to-≈ Reduction.red-fun

exp-fun≈ : (t : Tm Γ (a ⇒ b)) → t ≈ lam (app (wkTm fresh t) (var ze))
exp-fun≈ t = ⟶-to-≈ Reduction.exp-fun

red-box≈ : (t : Tm (ΓL 🔒) a) (e : LFExt Γ (ΓL 🔒) ΓR) → unbox (box t) e ≈ wkTm (LFExtTo≤ e) t
red-box≈ t e = ⟶-to-≈ Reduction.red-box

exp-box≈ : (t : Tm Γ (◻ a)) → t ≈ box (unbox t new)
exp-box≈ t = ⟶-to-≈ Reduction.exp-box

cong-lam≈ : ∀ (t≈t' : t ≈ t') → lam t ≈ lam t'
cong-lam≈ = cong-⟶-to-cong-≈ Reduction.cong-lam

cong-app1≈ : ∀ (t≈t' : t ≈ t') → app t u ≈ app t' u
cong-app1≈ = cong-⟶-to-cong-≈ Reduction.cong-app1

cong-app2≈ : ∀ (u≈u' : u ≈ u') → app t u ≈ app t u'
cong-app2≈ = cong-⟶-to-cong-≈ Reduction.cong-app2

cong-app≈ : ∀ (t≈t' : t ≈ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app≈ t≈t' u≈u' = trans-≈ (cong-app1≈ t≈t') (cong-app2≈ u≈u')

cong-box≈ : ∀ (t≈t' : t ≈ t') → box t ≈ box t'
cong-box≈ = cong-⟶-to-cong-≈ Reduction.cong-box

cong-unbox1≈ : ∀ (t≈t' : t ≈ t') → unbox t e ≈ unbox t' e
cong-unbox1≈ = cong-⟶-to-cong-≈ Reduction.cong-unbox

cong-unbox2≈ : ∀ (e≡e' : e ≡ e') → unbox t e ≈ unbox t e'
cong-unbox2≈ e≡e' = ≡-to-≈ (cong₂ unbox ≡-refl e≡e')

cong-unbox≈ : ∀ (t≈t' : t ≈ t') (e≡e' : e ≡ e') → unbox t e ≈ unbox t' e'
cong-unbox≈ t≈t' e≡e' = ≈-trans (cong-unbox1≈ t≈t') (cong-unbox2≈ e≡e')

--------------------
-- Derived equations
--------------------
