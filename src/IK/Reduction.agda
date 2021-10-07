module IK.Reduction where

open import IK.Term
open import IK.HellOfSyntacticLemmas
  using (beta-wk-lemma ; keepFreshLemma ; sliceCompLemma)

open import Relation.Nullary
  using (¬_)

open import Relation.Binary
  using (Preorder)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  as ReflexiveTransitive
  using (Star)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
  using (preorder)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; cong₂)

open ReflexiveTransitive public
  using (ε ; _◅_)

-------------------
-- Reduction rules
-------------------

data _⟶_ : Tm Γ a → Tm Γ a → Set where

  red-fun : {t : Tm (Γ `, a) b} {u : Tm Γ a}
    → app (lam t) u ⟶ substTm (idₛ `, u) t

  exp-fun : {t : Tm Γ (a ⇒ b)}
    → t ⟶ lam (app (wkTm fresh t) (var ze))

  red-box : {t : Tm (ΓL 🔒) a} {e : LFExt Γ (ΓL 🔒) ΓR}
    → unbox (box t) e ⟶ wkTm (LFExtTo≤ e) t

  exp-box : {t : Tm Γ (◻ a)}
    → t ⟶ box (unbox t nil)

  cong-lam : {t t' : Tm (Γ `, a) b}
    → t ⟶ t'
    → lam t ⟶ lam t'

  cong-app1 : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ a}
    → t ⟶ t'
    → app t u ⟶ app t' u

  cong-app2 : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ a}
    → u ⟶ u'
    → app t u ⟶ app t u'

  cong-box : {t t' : Tm (Γ 🔒) a}
    → t ⟶ t'
    → box t ⟶ box t'

  cong-unbox : {t t' : Tm ΓL (◻ a)} {e : LFExt Γ (ΓL 🔒) ΓR}
    → t ⟶ t'
    → unbox t e ⟶ unbox t' e

-- zero or more steps of reduction
Tm-preorder : (Γ : Ctx) → (a : Ty) → Preorder _ _ _
Tm-preorder Γ a = preorder (_⟶_ {Γ} {a})

module _ {Γ : Ctx} {a : Ty} where
  open Preorder (Tm-preorder Γ a) public
    using    ()
    renaming (_∼_ to _⟶*_ ; refl to ⟶-refl ; reflexive to zero ; trans to multi)

one : {t t' : Tm Γ a} → t ⟶ t' → t ⟶* t'
one t = t ◅ ε

module _ {t : Tm Γ a → Tm Δ b} (cong-t : ∀ {u u' : Tm Γ a} → (u⟶u' : u ⟶ u') → t u ⟶* t u') where
  cong-⟶*-to-cong-⟶* : ∀ (u⟶*u' : u ⟶* u') → t u ⟶* t u'
  cong-⟶*-to-cong-⟶* ε                 = ε
  cong-⟶*-to-cong-⟶* (u⟶u'' ◅ u''⟶*u') = multi (cong-t u⟶u'') (cong-⟶*-to-cong-⟶* u''⟶*u')

cong-⟶-to-cong-⟶* : {t : Tm Γ a → Tm Δ b} (cong-t : ∀ {u u' : Tm Γ a} → (u⟶u' : u ⟶ u') → t u ⟶ t u') (u⟶*u' : u ⟶* u') → t u ⟶* t u'
cong-⟶-to-cong-⟶* cong-t = cong-⟶*-to-cong-⟶* (λ u⟶u' → one (cong-t u⟶u'))

cong-app : {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → t ⟶ t' → u ⟶ u'
  → app t u ⟶* app t' u'
cong-app t⟶t' u⟶u' = cong-app1 t⟶t' ◅ cong-app2 u⟶u' ◅ ε

cong-box* : {t t' : Tm (Γ 🔒) a}
  → t ⟶* t'
  → box t ⟶* box t'
cong-box* = cong-⟶-to-cong-⟶* cong-box

cong-unbox* : {t t' : Tm ΓL (◻ a)} {e : LFExt Γ (ΓL 🔒) ΓR}
  → t ⟶* t'
  → unbox t e ⟶* unbox t' e
cong-unbox* = cong-⟶-to-cong-⟶* cong-unbox

cong-lam* : {t t' : Tm (Γ `, a) b}
  → t ⟶* t'
  → lam t ⟶* lam t'
cong-lam* = cong-⟶-to-cong-⟶* cong-lam

cong-app1* : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ  a}
  → t ⟶* t'
  → app t u ⟶* app t' u
cong-app1* = cong-⟶-to-cong-⟶* cong-app1

cong-app2* : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → u ⟶* u'
  → app t u ⟶* app t u'
cong-app2* = cong-⟶-to-cong-⟶* cong-app2

cong-app*  : {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → t ⟶* t' → u ⟶* u'
  → app t u ⟶* app t' u'
cong-app* t⟶*t' u⟶*u' = multi (cong-app1* t⟶*t') (cong-app2* u⟶*u')

invRed :  {t t' : Tm Γ a}
  → (w : Γ ⊆ Δ)
  → t ⟶ t'
  → wkTm w t ⟶* wkTm w t'
invRed w (red-fun {t = t} {u = u})
  = multi (one red-fun) (zero (beta-wk-lemma w u t))
invRed w exp-fun
  = multi (one exp-fun) (zero (cong lam (cong₂ app keepFreshLemma refl)))
invRed w (red-box {e = e})
  = multi (one red-box) (zero (sliceCompLemma w e _))
invRed w exp-box
  = one exp-box
invRed w (cong-lam r)
  = cong-lam* (invRed (keep w) r)
invRed w (cong-box r)
  = cong-box* (invRed (keep🔒 w) r)
invRed w (cong-unbox r)
  = cong-unbox* (invRed (sliceLeft _ w) r)
invRed w (cong-app1 r)
  = cong-app* (invRed w r) ε
invRed w (cong-app2 r)
  = cong-app* ε (invRed w r)

invRed* :  {t t' : Tm Γ a}
  → (w : Γ ⊆ Δ)
  → t ⟶* t'
  → wkTm w t ⟶* wkTm w t'
invRed* w = cong-⟶*-to-cong-⟶* (invRed w)
