{-# OPTIONS --allow-unsolved-metas #-}
module IS4.Reduction where

open import IS4.Term
open import IS4.HellOfSyntacticLemmas

open import Relation.Nullary
  using (¬_)

open import Relation.Binary
  using (Preorder)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  as ReflexiveTransitive
  using (Star)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
  using (preorder)
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open ReflexiveTransitive public
  using (ε ; _◅_)

-------------------
-- Reduction rules
-------------------

data _⟶_ : Tm Γ a → Tm Γ a → Set where

  red-fun : (t : Tm (Γ `, a) b) (u : Tm Γ a)
    → app (lam t) u ⟶ substTm (idₛ `, u) t

  exp-fun : (t : Tm Γ (a ⇒ b))
    → t ⟶ lam (app (wkTm fresh t) (var ze))

  red-box : (t : Tm (ΓL 🔒) a) (e : CExt Γ ΓL ΓR)
    → unbox (box t) e ⟶ substTm (lock idₛ e) t

  exp-box : (t : Tm Γ (◻ a))
    → t ⟶ box (unbox t new)

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

  cong-unbox : {t t' : Tm ΓL (◻ a)} {e : CExt Γ ΓL ΓR}
    → t ⟶ t'
    → unbox t e ⟶ unbox t' e

  fact-unbox : {t : Tm ΓL (◻ a)} {e : CExt Γ ΓL ΓR}
    → unbox t e ⟶ unbox (substTm (factorSubₛ e idₛ) t) (factorExtₛ e idₛ)


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

cong-unbox* : {t t' : Tm ΓL (◻ a)} {e : CExt Γ ΓL ΓR}
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

data _⟶ₛ*_ : Sub Δ Γ → Sub Δ Γ → Set where
  ε          : {s : Sub Δ Γ}
    → s ⟶ₛ* s
  multiₛ      : {s s' s'' : Sub Δ Γ}
    → s ⟶ₛ* s' → s' ⟶ₛ* s'' → s ⟶ₛ* s''
  cong-`,*   : {s s' : Sub Δ Γ} {t t' : Tm Δ a}
    → s ⟶ₛ* s' → t ⟶* t' → (s `, t) ⟶ₛ* (s' `, t')
  cong-lock*  : {s s' : Sub ΔL ΓL} {e : CExt Δ ΔL ΔR}
    → s ⟶ₛ* s' → lock s e ⟶ₛ* lock s' e
  fact-lock* : {s : Sub ΔL ΓL} {e : CExt Δ ΔL ΔR}
    → lock s e ⟶ₛ* lock (s ∙ₛ factorSubₛ e idₛ) (factorExtₛ e idₛ)

zeroₛ : {s s' : Sub Δ Γ} → s ≡ s' → s ⟶ₛ* s'
zeroₛ refl = ε

substTmPresId : (t : Tm Γ a) → t ⟶* substTm idₛ t
substTmPresId (var x)     = zero (sym (substVarPresId x))
substTmPresId (lam t)     = cong-lam* (substTmPresId t)
substTmPresId (app t u)   = cong-app* (substTmPresId t) (substTmPresId u)
substTmPresId (box t)     = cong-box* (substTmPresId t)
substTmPresId (unbox t e) = one fact-unbox

rightIdSub : (s : Sub Γ Γ') → s ⟶ₛ* (s ∙ₛ idₛ)
rightIdSub []         = ε
rightIdSub (s `, t)   = cong-`,* (rightIdSub s) (substTmPresId t)
rightIdSub (lock s e) = fact-lock*

invRed :  {t t' : Tm Γ a}
  → (w : Γ ⊆ Γ')
  → t ⟶ t'
  → wkTm w t ⟶* wkTm w t'
invRed w (red-fun t u)
  = multi (one (red-fun _ _)) (zero (beta-wk-lemma w u t))
invRed w (exp-fun _)
  = multi (one (exp-fun _)) (zero (cong lam (cong₂ app keepFreshLemma refl)))
invRed w (red-box t e)
  = multi (one (red-box _ _)) (zero (trans (trans (sym (coh-trimSub-wkTm t _ _)) {!!}) (nat-substTm t _ w)))
  -- use `coh-trimSub-wkSub idₛ idₛ (factorWk e w)` and substitution identities
invRed w (exp-box _)
  = one (exp-box _)
invRed w (cong-lam r)
  = cong-lam* (invRed (keep w) r)
invRed w (cong-box r)
  = cong-box* (invRed (keep🔒 w) r)
invRed w (cong-unbox {e = e} r)
  = cong-unbox* (invRed (factorWk e w ) r)
invRed w (cong-app1 r)
  = cong-app* (invRed w r) ε
invRed w (cong-app2 r)
  = cong-app* ε (invRed w r)
invRed w fact-unbox = {!!}

wkTmPres⟶* :  {t t' : Tm Γ a}
  → (w : Γ ⊆ Γ')
  → t ⟶* t'
  → wkTm w t ⟶* wkTm w t'
wkTmPres⟶* w = cong-⟶*-to-cong-⟶* (invRed w)
