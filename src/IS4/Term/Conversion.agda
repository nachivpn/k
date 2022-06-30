{-# OPTIONS --safe --without-K #-}
module IS4.Term.Conversion where

open import Data.Product using (Σ ; _,_)

import Data.Sum as Sum

open import Relation.Binary using (Setoid)

open import Relation.Binary.Construct.Closure.Equivalence using (setoid)
import      Relation.Binary.Construct.Closure.Equivalence.Properties as EquivalenceProperties

import Relation.Binary.Construct.Closure.ReflexiveTransitive as ReflexiveTransitive

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; subst ; subst₂ ; module ≡-Reasoning)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

open import PUtil

open import IS4.Term.Base
open import IS4.Term.Reduction as Reduction

open Sum                   public using (inj₁ ; inj₂)
open ReflexiveTransitive   public using (ε ; _◅_)
open EquivalenceProperties public using () renaming (a—↠b⇒a↔b to ⟶*-to-≈)

-- Convertibility is defined by taking the equivalence closure of the
-- reduction relation `_⟶_`, i.e. two terms `t` and `u` are
-- convertible (written `t ≈ u`) if and only if there is a sequence of
-- terms `sᵢ` for i = 0,…,n such that 1. `s₀ = t`, 2. `sₙ = u`, and
-- 3. `sᵢ ⟶ sᵢ₊₁` or `sᵢ₊₁ ⟶ sᵢ` for all i.
--
-- Note that `_⟶_` is already a congruence, i.e. `u ⟶ v` implies `t[u]
-- ⟶ t[v]`, and being a congruence preserved by closing under
-- reflexivity, symmetry and transitivity.
Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
Tm-setoid Γ a = setoid (_⟶_ {Γ} {a})

module _ {Γ : Ctx} {a : Ty} where
  open Setoid (Tm-setoid Γ a) public
    using    (_≈_)
    renaming (refl to ≈-refl ; reflexive to ≈-reflexive ; sym to ≈-sym ; trans to ≈-trans ; isEquivalence to ≈-equiv)

  ≈-reflexive˘ : t' ≡ t → t ≈ t'
  ≈-reflexive˘ t'≡t = ≈-reflexive (≡-sym t'≡t)

  ≡-to-≈ = ≈-reflexive

  ≈-˘trans : t' ≈ t → t' ≈ t'' → t ≈ t''
  ≈-˘trans t'≈t t'≈t'' = ≈-trans (≈-sym t'≈t) t'≈t''

  ≈-trans˘ : t ≈ t' → t'' ≈ t' → t ≈ t''
  ≈-trans˘ t≈t' t''≈t' = ≈-trans t≈t' (≈-sym t''≈t')

  ≡-≈-trans˘ : t ≡ t' → t'' ≈ t' → t ≈ t''
  ≡-≈-trans˘ t≡t' t''≈t' = ≈-trans˘ (≡-to-≈ t≡t') t''≈t'

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

red-box≈ : (t : Tm (ΓL #) a) (e : CExt Γ ΓL ΓR) → unbox (box t) e ≈ substTm (lock idₛ e) t
red-box≈ t e = ⟶-to-≈ (Reduction.red-box t e)

exp-box≈ : (t : Tm Γ (□ a)) → t ≈ box (unbox t new)
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

cong-unbox2≈ : ∀ {t : Tm Γ (□ a)} {e : CExt Δ Γ ΓR} {e' : CExt Δ Γ ΓR'} → unbox t e ≈ unbox t e'
cong-unbox2≈ {t = t} {e} {e'} = subst (λ (_ , e') → unbox t e ≈ unbox t e') (Σ-≡,≡→≡ (extRUniq e e' , ExtIsProp′ e e')) ≈-refl

cong-unbox≈ : ∀ (t≈t' : t ≈ t') → unbox t e ≈ unbox t' e'
cong-unbox≈ t≈t' = ≈-trans (cong-unbox1≈ t≈t') cong-unbox2≈

dcong-unbox≈ : ∀ (Γ≡Γ' : Γ ≡ Γ') (t≈t' : subst (λ Γ → Tm Γ (□ a)) Γ≡Γ' t ≈ t') → unbox t e ≈ unbox t' e'
dcong-unbox≈ ≡-refl = cong-unbox≈

shift-unbox≈ : ∀ (t : Tm Γ (□ a)) (w : LFExt Γ' Γ ΓR) → unbox t e ≈ unbox (wkTm (LFExtToWk w) t) e'
shift-unbox≈ t w = ≈-trans cong-unbox2≈ (⟶-to-≈ (Reduction.shift-unbox t w _))

----------------------------------------------------------------------
-- Congruence closure of the relation that identifies substitutions up
-- to "built-in" weakenings (see `shift-lock≈ₛ`)
----------------------------------------------------------------------

data _⟶ₛ_ : Sub Δ Γ → Sub Δ Γ → Set where
  cong-`,⟶ₛ1   : {s s' : Sub Δ Γ} {t : Tm Δ a}
    → s ⟶ₛ s' → (s `, t) ⟶ₛ (s' `, t)
  cong-`,⟶ₛ2   : {s : Sub Δ Γ} {t t' : Tm Δ a}
    → t ≈ t' → (s `, t) ⟶ₛ (s `, t')
  cong-lock⟶ₛ  : {s s' : Sub ΔL ΓL} {e : CExt Δ ΔL ΔR}
    → s ⟶ₛ s' → lock s e ⟶ₛ lock s' e
  shift-lock⟶ₛ : {ΔLL ΔLR : Ctx} {s : Sub ΔLL Γ} (w : LFExt ΔL ΔLL ΔLR) {e : CExt Δ ΔL ΔR}
    → lock s (extRAssoc (upLFExt w) e) ⟶ₛ lock (wkSub (LFExtToWk w) s) e

Sub-setoid : (Δ Γ : Ctx) → Setoid _ _
Sub-setoid Δ Γ = setoid (_⟶ₛ_ {Δ} {Γ})

module _ {Δ Γ : Ctx} where
  open Setoid (Sub-setoid Δ Γ) public
    using ()
    renaming (_≈_ to _≈ₛ_ ; reflexive to ≈ₛ-reflexive ; refl to ≈ₛ-refl ; sym to ≈ₛ-sym ; trans to ≈ₛ-trans)

  ≈ₛ-reflexive˘ : σ' ≡ σ → σ ≈ₛ σ'
  ≈ₛ-reflexive˘ σ'≡σ = ≈ₛ-reflexive (≡-sym σ'≡σ)

⟶ₛ-to-≈ₛ : σ ⟶ₛ σ' → σ ≈ₛ σ'
⟶ₛ-to-≈ₛ p = inj₁ p ◅ ε

module _ {σ : Sub Δ Γ → Sub Δ' Γ'} (cong-σ : ∀ {τ τ' : Sub Δ Γ} → (τ⟶τ' : τ ⟶ₛ τ') → σ τ ⟶ₛ σ τ') where
  -- XXX: fold
  cong-⟶ₛ-to-cong-≈ₛ : ∀ (τ≈τ' : τ ≈ₛ τ') → σ τ ≈ₛ σ τ'
  cong-⟶ₛ-to-cong-≈ₛ ε                     = ε
  cong-⟶ₛ-to-cong-≈ₛ (inj₁ τ⟶τ'' ◅ τ''≈τ') = inj₁ (cong-σ τ⟶τ'') ◅ cong-⟶ₛ-to-cong-≈ₛ τ''≈τ'
  cong-⟶ₛ-to-cong-≈ₛ (inj₂ τ⟵τ'' ◅ τ''≈τ') = inj₂ (cong-σ τ⟵τ'') ◅ cong-⟶ₛ-to-cong-≈ₛ τ''≈τ'

cong-`,1≈ₛ : (σ≈σ' : σ ≈ₛ σ') → (σ `, t) ≈ₛ (σ' `, t)
cong-`,1≈ₛ = cong-⟶ₛ-to-cong-≈ₛ cong-`,⟶ₛ1

cong-`,2≈ₛ : (t≈t' : t ≈ t') → (σ `, t) ≈ₛ (σ `, t')
cong-`,2≈ₛ t≈t' = ⟶ₛ-to-≈ₛ (cong-`,⟶ₛ2 t≈t')

cong-`,≈ₛ : (σ≈σ' : σ ≈ₛ σ') → (t≈t' : t ≈ t') → (σ `, t) ≈ₛ (σ' `, t')
cong-`,≈ₛ σ≈σ' t≈t' = ≈ₛ-trans (cong-`,1≈ₛ σ≈σ') (cong-`,2≈ₛ t≈t')

cong-lock≈ₛ : (σ≈σ' : σ ≈ₛ σ') → lock σ e ≈ₛ lock σ' e
cong-lock≈ₛ = cong-⟶ₛ-to-cong-≈ₛ cong-lock⟶ₛ

shift-lock≈ₛ : (w : LFExt Δ' Δ ΔR) → lock σ (extRAssoc (upLFExt w) e) ≈ₛ lock (wkSub (LFExtToWk w) σ) e
shift-lock≈ₛ w = ⟶ₛ-to-≈ₛ (shift-lock⟶ₛ w)

--------------------
-- Derived equations
--------------------
