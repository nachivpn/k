module IS4.Term.Conversion where

open import IS4.Term.Base
open import IS4.Term.Reduction
  as Reduction

import Data.Sum as Sum

open import Relation.Nullary
  using (¬_)

open import Relation.Binary
  using (Setoid)

open import Relation.Binary.Construct.Closure.Equivalence
  using (setoid)
import Relation.Binary.Construct.Closure.Equivalence.Properties
  as EquivalenceProperties

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  as ReflexiveTransitive
  using (Star)

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

open Sum public
  using (inj₁ ; inj₂)
open ReflexiveTransitive public
  using (ε ; _◅_)
open EquivalenceProperties public
  using    ()
  renaming (a—↠b⇒a↔b to ⟶*-to-≈)

-- Convertibility is defined taking the
-- equivalence closure of the reduction relation.
Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
Tm-setoid Γ a = setoid (_⟶_ {Γ} {a})

module _ {Γ : Ctx} {a : Ty} where
  open Setoid (Tm-setoid Γ a) public
    using    (_≈_)
    renaming (refl to ≈-refl ; reflexive to ≡-to-≈ ; sym to ≈-sym ; trans to ≈-trans ; isEquivalence to ≈-equiv)

≡˘-to-≈ : t' ≡ t → t ≈ t'
≡˘-to-≈ t'≡t = ≡-to-≈ (≡-sym t'≡t)

⟶-to-≈ : t ⟶ t' → t ≈ t'
⟶-to-≈ p = inj₁ p ◅ ε

⟵-to-≈ : t' ⟶ t → t ≈ t'
⟵-to-≈ p = inj₂ p ◅ ε

module _ {t : Tm Γ a → Tm Δ b} (cong-t : ∀ {u u' : Tm Γ a} → (u⟶u' : u ⟶ u') → t u ⟶ t u') where
  -- XXX: fold
  cong-⟶-to-cong-≈ : ∀ (u≈u' : u ≈ u') → t u ≈ t u'
  cong-⟶-to-cong-≈ ε                     = ε
  cong-⟶-to-cong-≈ (inj₁ u⟶u'' ◅ u''≈u') = inj₁ (cong-t u⟶u'') ◅ cong-⟶-to-cong-≈ u''≈u'
  cong-⟶-to-cong-≈ (inj₂ u⟵u'' ◅ u''≈u') = inj₂ (cong-t u⟵u'') ◅ cong-⟶-to-cong-≈ u''≈u'

red-fun≈ : (t : Tm (Γ `, a) b) (u : Tm Γ a) → (app (lam t) u) ≈ substTm (idₛ `, u) t
red-fun≈ t u = ⟶-to-≈ (Reduction.red-fun t u)

exp-fun≈ : (t : Tm Γ (a ⇒ b)) → t ≈ lam (app (wkTm fresh t) (var ze))
exp-fun≈ t = ⟶-to-≈ (Reduction.exp-fun t)

red-box≈ : (t : Tm (ΓL 🔒) a) (e : CExt Γ ΓL ΓR) → unbox (box t) e ≈ substTm (lock idₛ e) t
red-box≈ t e = ⟶-to-≈ (Reduction.red-box t e)

exp-box≈ : (t : Tm Γ (◻ a)) → t ≈ box (unbox t new)
exp-box≈ t = ⟶-to-≈ (Reduction.exp-box t)

cong-lam≈ : ∀ (t≈t' : t ≈ t') → lam t ≈ lam t'
cong-lam≈ = cong-⟶-to-cong-≈ Reduction.cong-lam

cong-app1≈ : ∀ (t≈t' : t ≈ t') → app t u ≈ app t' u
cong-app1≈ = cong-⟶-to-cong-≈ Reduction.cong-app1

cong-app2≈ : ∀ (u≈u' : u ≈ u') → app t u ≈ app t u'
cong-app2≈ = cong-⟶-to-cong-≈ Reduction.cong-app2

cong-app≈ : ∀ (t≈t' : t ≈ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app≈ t≈t' u≈u' = ≈-trans (cong-app1≈ t≈t') (cong-app2≈ u≈u')

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