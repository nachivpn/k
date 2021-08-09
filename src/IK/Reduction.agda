module IK.Reduction where

open import IK.Term
open import IK.HellOfSyntacticLemmas
  using (beta-wk-lemma ; keepFreshLemma ; sliceCompLemma)

open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to multi) public

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂)

open Star
open _≡_

-------------------
-- Reduction rules
-------------------

data _⟶_ : Tm Γ a → Tm Γ a → Set where

  red-fun : {t : Tm (Γ `, a) b} {u : Tm Γ a}
    → (app (lam t) u) ⟶ substTm (idₛ `, u) t

  exp-fun : {t : Tm Γ (a ⇒ b)}
    → t ⟶ lam (app (wkTm fresh t) (var ze))

  red-box : {t : Tm (ΓL 🔒) a} {e : LFExt Γ (ΓL 🔒) ΓR}
    → unbox (box t) e ⟶ wkTm (LFExtTo≤ e) t

  exp-box : {t : Tm Γ (◻ a)}
    → t ⟶ box (unbox t nil)

  cong-lam : {t t' : Tm (Γ `, a) b}
    → t ⟶ t'
    → (lam t) ⟶ (lam t')

  cong-app1 : {t t' : Tm Γ (a ⇒ b)} {u : Tm Γ a}
    → t ⟶ t'
    → (app t u) ⟶ (app t' u)

  cong-app2 : {t : Tm Γ (a ⇒ b)} {u u' : Tm Γ a}
    → u ⟶ u'
    → (app t u) ⟶ (app t u')

  cong-box : {t t' : Tm (Γ 🔒) a}
    → t ⟶ t'
    → (box t) ⟶ (box t')

  cong-unbox : {t t' : Tm ΓL (◻ a)} {e : LFExt Γ (ΓL 🔒) ΓR}
    → t ⟶ t'
    → (unbox t e) ⟶ (unbox t' e)


-- zero or more steps of reduction
_⟶*_ : Tm Γ a → Tm Γ a → Set
_⟶*_ = Star (_⟶_)

zero : {t t' : Tm Γ a} → t ≡ t' → t ⟶* t'
zero refl = ε

one : {t t' : Tm Γ a} → t ⟶ t' → t ⟶* t'
one t = t Star.◅ ε

cong-box* : {t t' : Tm (Γ 🔒) a}
  → t ⟶* t'
  → (box t) ⟶* (box t')
cong-box* ε       = ε
cong-box* (x ◅ r) = cong-box x ◅ cong-box* r

cong-unbox* : {t t' : Tm ΓL (◻ a)} {e : LFExt Γ (ΓL 🔒) ΓR}
  → t ⟶* t'
  → (unbox t e) ⟶* (unbox t' e)
cong-unbox* ε       = ε
cong-unbox* (x ◅ r) = cong-unbox x ◅ cong-unbox* r

cong-lam* : {t t' : Tm (Γ `, a) b}
  → t ⟶* t'
  → (lam t) ⟶* (lam t')
cong-lam* ε       = ε
cong-lam* (x ◅ r) = cong-lam x ◅ cong-lam* r

cong-app*  : {t t' : Tm Γ (a ⇒ b)} {u u' : Tm Γ  a}
  → t ⟶* t' → u ⟶* u'
  → (app t u) ⟶* (app t' u')
cong-app* ε        ε        = ε
cong-app* (x ◅ r1) ε        = cong-app1 x ◅ cong-app* r1 ε
cong-app* r1       (x ◅ r2) = cong-app2 x ◅ cong-app* r1 r2


invRed :  {t t' : Tm Γ a}
  → (w : Δ ≤ Γ)
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
  → (w : Δ ≤ Γ)
  → t ⟶* t'
  → wkTm w t ⟶* wkTm w t'
invRed* w ε       = ε
invRed* w (x ◅ r) = multi (invRed w x) (invRed* w r)
