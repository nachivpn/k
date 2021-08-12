--{-# OPTIONS --allow-unsolved-metas #-}

module IK.Soundness.Soundness where

open import Data.Unit
  using (⊤ ; tt)
open import Data.Product
  using (Σ ; _×_ ; _,_ ; ∃)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
  renaming (_◅◅_ to multi) public

open Star

import Context
open import IK.Term
open import IK.Norm
open import IK.Reduction
open import IK.Soundness.Presheaf
open import IK.HellOfSyntacticLemmas

-- soundness relation on semantic values
_≋_ : Tm' Γ a → Tm' Γ a → Set
_≋_ {Γ} {a = 𝕓}      n       m
  = n ≡ m
_≋_ {Γ} {a = a ⇒ b}  f       g
  = {Γ' : Ctx} (w : Γ' ≤ Γ) → {x y : Tm' Γ' a}
    → Psh x → Psh y
    → x ≋ y → f w x ≋ g w y
_≋_ {Γ} {a = ◻ a}    (box x) (box y)
  = x ≋ y

-- soundness relation on semantic substitutions
data _≋ₛ_ : Sub' Γ Δ → Sub' Γ Δ → Set where
  []   : _≋ₛ_ {Γ = Γ} {Δ = []} tt tt
  _`,_ : {s : Sub' Γ Δ} {s' : Sub' Γ Δ} {x : Tm' Γ a} {y : Tm' Γ a}
       → s ≋ₛ s' → x ≋ y → (s , x) ≋ₛ (s' , y)
  lock : {s : Sub' Γ Δ} {s' : Sub' Γ Δ}
       → s ≋ₛ s' → (e : LFExt Γ' (Γ 🔒) (ΓR))
       → _≋ₛ_ {Γ = Γ'} {Δ = Δ 🔒} (lock s e)  (lock s' e)

-- wkTm' preserves the relation _≋_
wkTm'Pres≋ : {x : Tm' Γ a} {y : Tm' Γ a}
  → (w : Δ ≤ Γ)
  → x ≋ y
  → wkTm' w x ≋ wkTm' w y
wkTm'Pres≋ {a = 𝕓}                           w x≡y
  = cong (wkNf w) x≡y
wkTm'Pres≋ {a = a ⇒ b} {x = f} {y = g}       w f≋g
  = λ w' px py x≋y → f≋g (w ∙ w') px py x≋y
wkTm'Pres≋ {a = ◻ a} {x = box x} {y = box y} w x≋y
  = wkTm'Pres≋ {a = a} (keep🔒 w) x≋y

-- wkSub' preserves the relation _≋_
wkSub'Pres≋ : {s s' : Sub' Γ Δ}
  → (w : Γ' ≤ Γ)
  → s ≋ₛ s'
  → wkSub' w s ≋ₛ wkSub' w s'
wkSub'Pres≋ w []
  = []
wkSub'Pres≋ {Δ = Δ `, a} w (s≋s' `, x)
  = wkSub'Pres≋ w s≋s' `, wkTm'Pres≋ {a = a} w x
wkSub'Pres≋ w (lock s≋s e)
  = lock (wkSub'Pres≋ (sliceLeft e w) s≋s) (wkLFExt e w)

private

  substVar'Pres≋ : (x : Var Γ a) {s s' : Sub' Δ Γ}
    → s ≋ₛ s'
    → substVar' x s ≋ substVar' x s'
  substVar'Pres≋ ze     {s = _ , x} {s' = _ , y}  (_ `, x≋y)
    = x≋y
  substVar'Pres≋ (su x) {s = s , _} {s' = s' , _} (s≋s' `, _)
    = substVar'Pres≋ x s≋s'

  unbox'Pres≋ : {x y : Box (Tm'- a) Γ}
    → (e : LFExt Γ' (Γ 🔒) ΓR)
    → x ≋ y
    → unbox' x e ≋ unbox' y e
  unbox'Pres≋ {a = a} {x = box x} {y = box y} e x≋y
    = wkTm'Pres≋ {a = a} (LFExtTo≤ e) x≋y
  
-- 
fund :  (t : Tm Γ a) {s s' : Sub' Δ Γ}
  → Pshₛ s → Pshₛ s'
  → s ≋ₛ s' → eval t s ≋ eval t s'
fund (var x) ps ps' s≋s'
  = substVar'Pres≋ x s≋s'
fund (lam t) {s = s} {s' = s'} ps ps' s≋s'
  = λ w px py x≋y
    → fund t
           (wkSub'PresPsh w s ps , px)
           (wkSub'PresPsh w s' ps' , py)
           (wkSub'Pres≋ w s≋s' `, x≋y)
fund (app t u) {s = s} {s' = s'} ps ps' s≋s'
  = fund t ps ps' s≋s' idWk (psh-eval u s ps) (psh-eval u s' ps') (fund u ps ps' s≋s')
fund (box t) ps ps' s≋s'
  = fund t ps ps' (lock s≋s' nil)
fund (unbox t nil) {s = lock s e} {s' = lock s' .e} ps ps' (lock s≋s' .e)
  = unbox'Pres≋ {x = eval t s} e (fund t ps ps' s≋s')
fund (unbox t (ext e)) (ps , _) (ps' , _) (s≋s' `, _)
  = fund (unbox t e) ps ps' s≋s'

trimSub' : Γ' ≤ Γ → Sub'- Γ' →̇ Sub'- Γ
trimSub' base      tt         = tt
trimSub' (drop w)  (s , _)    = trimSub' w s
trimSub' (keep w)  (s , x)    = trimSub' w s , x
trimSub' (keep🔒 w) (lock s e) = lock (trimSub' w s) e

nat-trimSub' : (w' : Δ ≤ Δ') (w : Γ' ≤ Γ) (s : Sub' Γ Δ)
  → trimSub' w' (wkSub' w s) ≡ wkSub' w (trimSub' w' s)
nat-trimSub' base       w s          = refl
nat-trimSub' (drop w')  w (s , _)    = nat-trimSub' w' w s
nat-trimSub' (keep w')  w (s , x)    = cong₂ _,_ (nat-trimSub' w' w s) refl
nat-trimSub' (keep🔒 w') w (lock s e) = cong₂ lock (nat-trimSub' w' (sliceLeft e w) s) refl

trimSub'PresId : (s : Sub' Γ Δ) → trimSub' idWk s ≡ s
trimSub'PresId {Δ = []}     tt         = refl
trimSub'PresId {Δ = Δ `, _} (s , _)    = cong₂ _,_ (trimSub'PresId s) refl
trimSub'PresId {Δ = Δ 🔒}    (lock s e) = cong₂ lock (trimSub'PresId s) refl

-- semantic version of `coh-trimSub-wkVar` in `Substitution.agda`
coh-trimSub'-wkVar' : (w : Γ' ≤ Γ) (s : Sub' Δ Γ') (x : Var Γ a)
  → substVar' (wkVar w x) s ≡ substVar' x (trimSub' w s)
coh-trimSub'-wkVar' (drop w) (s , _) ze     = coh-trimSub'-wkVar' w s ze
coh-trimSub'-wkVar' (drop w) (s , _) (su x) = coh-trimSub'-wkVar' w s (su x)
coh-trimSub'-wkVar' (keep w) (s , _) ze     = refl
coh-trimSub'-wkVar' (keep w) (s , _) (su x) = coh-trimSub'-wkVar' w s x

-- semantic version of `coh-trimSub-wkTm` in `HellOfSyntacticLemmas.agda`
coh-trimSub'-wkTm : (w : Γ' ≤ Γ) (s : Sub' Δ Γ') (t : Tm Γ a)
  → eval (wkTm w t) s ≡ eval t (trimSub' w s)
coh-trimSub'-wkTm w s (var x)
  = coh-trimSub'-wkVar' w s x
coh-trimSub'-wkTm w s (lam t)
  = funexti (λ _ → funext (λ w' → funext (λ x →
      trans
        (coh-trimSub'-wkTm (keep w) (wkSub' w' s , x) t)
        (cong (λ z → eval t (z , x)) (nat-trimSub' w w' s)))))
coh-trimSub'-wkTm w s (app t u)
  = trans
      (cong (λ f → f idWk (eval (wkTm w u) s)) (coh-trimSub'-wkTm w s t))
      (cong (eval t (trimSub' w s) idWk) (coh-trimSub'-wkTm w s u))
coh-trimSub'-wkTm w s (box t)
  = cong box (coh-trimSub'-wkTm (keep🔒 w) (lock s nil) t)
coh-trimSub'-wkTm (drop w) (s , _) (unbox t e)
  = coh-trimSub'-wkTm w s (unbox t e)
coh-trimSub'-wkTm (keep🔒 w) (lock s e) (unbox t nil)
  = cong₂ unbox' (coh-trimSub'-wkTm w s t) refl
coh-trimSub'-wkTm (keep w) (s , _) (unbox t (ext e))
  = coh-trimSub'-wkTm w s (unbox t e)
  
-- soundness of single-step reduction
sound-red : {t t' : Tm Γ a} {s s' : Sub' Δ Γ}
  → t ⟶ t'
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t s ≋ eval t' s'
sound-red red-fun ps ps' s≋s'
  = {!!} -- requires nat-evalₛ
sound-red {t = t} {s = s} {s'} exp-fun  ps ps' s≋s' w {x = x} px py x≋y rewrite
  sym (rightIdWk w)
  | sym (cong (λ f → f idWk x) (nat-eval t w s ps))
  | sym (trimSub'PresId (wkSub' w s))
  | rightIdWk w
  | sym (coh-trimSub'-wkTm fresh (wkSub' w s , x) t)
    = fund (wkTm (drop idWk) t)
           (wkSub'PresPsh w s ps , px)
           (wkSub'PresPsh w s' ps' , py)
           (wkSub'Pres≋ w s≋s' `, x≋y)
           idWk
           px
           py
           x≋y
sound-red red-box ps ps' s≋s'
  = {!!}
sound-red exp-box ps ps' s≋s'
  = {!!}
sound-red {t = t} {s = s} {s'} (cong-lam r) ps ps' s≋s' w {x = x} px py x≋y
  = sound-red r (wkSub'PresPsh w s ps , px) (wkSub'PresPsh w s' ps' , py) ((wkSub'Pres≋ w s≋s') `, x≋y)
sound-red {t = app t u} {t' = app t' u'} {s = s} {s' = s'} (cong-app1 r) ps ps' s≋s'
  = sound-red r ps ps' s≋s'
              idWk
              (psh-eval u s ps)
              (psh-eval u s' ps')
              (fund u ps ps' s≋s')
sound-red {t = app t u} {t' = app t' u'} {s = s} {s' = s'} (cong-app2 r) ps ps' s≋s'
  = fund t ps ps' s≋s' idWk (psh-eval u s ps) (psh-eval u' s' ps') (sound-red r ps ps' s≋s')
sound-red (cong-box r) ps ps' s≋s'
  = sound-red r ps ps' (lock s≋s' nil)
sound-red {s = lock s e} {s' = lock s' .e} (cong-unbox {t = t} {e = nil} r) ps ps' (lock s≋s' e)
  = unbox'Pres≋ {x = eval t s} e (sound-red r ps ps' s≋s')
sound-red {s = s , _} {s' = s' , _} (cong-unbox {t = t} {e = ext e} r) (ps , _) (ps' , _) (s≋s' `, _)
  = sound-red (cong-unbox {e = e} r) ps ps' s≋s'

-- soundness of multi-step reduction
sound-red* : {t t' : Tm Γ a} {s s' : Sub' Δ Γ}
  → t ⟶* t'
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t s ≋ eval t' s'
sound-red* {t = t} {t' = .t} ε        ps ps' s≋s'
  = fund t ps ps' s≋s'
sound-red* {t = t} {t' = t'} (r ◅ rs) ps ps' s≋s'
  = {!!} -- requires transitivity of ≋

