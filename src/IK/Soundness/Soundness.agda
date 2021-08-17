--{-# OPTIONS --allow-unsolved-metas #-}

module IK.Soundness.Soundness where

open import Data.Unit
  using (⊤ ; tt)
open import Data.Sum
  using (inj₁ ; inj₂)
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
open import IK.Conversion
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

-- ≋ is symmetric
sym-≋ : {x y : Tm' Γ a}
      → x ≋ y → y ≋ x
sym-≋ {a = 𝕓}     x≡y
  = sym x≡y
sym-≋ {a = a ⇒ b} x≋y
  = λ w px' py' x'≋y' → sym-≋ {a = b} (x≋y w py' px' (sym-≋ {a = a} x'≋y'))
sym-≋ {a = ◻ a} {box x} {box y} x≋y
  = sym-≋ {a = a} x≋y

-- ≋ is transitive
trans-≋ : {x y z : Tm' Γ a}
  → x ≋ y → y ≋ z → x ≋ z
trans-≋ {a = 𝕓}     x≡y y≡z
  = trans x≡y y≡z
trans-≋ {a = a ⇒ b} {x} {y} {z} x≋y y≋z w {x = x'} {y = y'} px' py' x'≋y'
  = trans-≋ {a = b} (x≋y w px' py' x'≋y' ) (y≋z w py' py' ((trans-≋ {a = a} (sym-≋ {a = a} x'≋y') x'≋y')))
trans-≋ {a = ◻ a} {box x} {box y} {box z} x≋y y≋z
  = trans-≋ {x = x} x≋y y≋z

-- WTH is this thing actually called?
pseudo-refl-≋ : {x y : Tm' Γ a}
  → x ≋ y → x ≋ x
pseudo-refl-≋ {a = a} x≋y = trans-≋ {a = a} x≋y (sym-≋ {a = a} x≋y)

-- ≋ₛ is symmetric
sym-≋ₛ : {s s' : Sub' Γ Δ}
      → s ≋ₛ s' → s' ≋ₛ s
sym-≋ₛ {Δ = []}     s≋s'
  = s≋s'
sym-≋ₛ {Δ = Δ `, a} {s = s , x} {s' = s' , y} (s≋s' `, x≋y)
  = sym-≋ₛ s≋s' `, sym-≋ {a = a} x≋y
sym-≋ₛ {Δ = Δ 🔒} {s = lock s e} {s' = lock s' .e}  (lock s≋s' .e)
  = lock (sym-≋ₛ s≋s') e

postulate
  -- ≋ₛ is transitive
  trans-≋ₛ : {s s' s'' : Sub' Γ Δ}
    → s ≋ₛ s' → s' ≋ₛ s'' → s ≋ₛ s''

pseudo-refl-≋ₛ : {s s' : Sub' Γ Δ}
  → s ≋ₛ s' → s ≋ₛ s
pseudo-refl-≋ₛ x≋y = trans-≋ₛ x≋y (sym-≋ₛ x≋y)


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

--
fundₛ :  (s₀ : Sub Γ Δ) {s s' : Sub' Δ' Γ}
  → Pshₛ s → Pshₛ s'
  → s ≋ₛ s' → evalₛ s₀ s ≋ₛ evalₛ s₀ s'
fundₛ []          ps ps' s≋s'
  = []
fundₛ (s₀ `, t)   ps ps' s≋s'
  = (fundₛ s₀ ps ps' s≋s') `, fund t ps ps' s≋s'
fundₛ (lock s₀ (ext e)) {s = s , _} {s' = s' , _} (ps , _) (ps' , _) (s≋s' `, _)
  = fundₛ (lock s₀ e) ps ps' s≋s'
fundₛ (lock s₀ nil) {s = lock s e} {s' = lock s' e} ps ps' (lock s≋s' e)
  = lock (fundₛ s₀ ps ps' s≋s') e

-- semantic counterpart of trimSub
trimSub' : Γ' ≤ Γ → Sub'- Γ' →̇ Sub'- Γ
trimSub' base      tt         = tt
trimSub' (drop w)  (s , _)    = trimSub' w s
trimSub' (keep w)  (s , x)    = trimSub' w s , x
trimSub' (keep🔒 w) (lock s e) = lock (trimSub' w s) e

-- naturality of trimSub'
nat-trimSub' : (w' : Δ ≤ Δ') (w : Γ' ≤ Γ) (s : Sub' Γ Δ)
  → trimSub' w' (wkSub' w s) ≡ wkSub' w (trimSub' w' s)
nat-trimSub' base       w s          = refl
nat-trimSub' (drop w')  w (s , _)    = nat-trimSub' w' w s
nat-trimSub' (keep w')  w (s , x)    = cong₂ _,_ (nat-trimSub' w' w s) refl
nat-trimSub' (keep🔒 w') w (lock s e) = cong₂ lock (nat-trimSub' w' (sliceLeft e w) s) refl

-- trimSub' preserves idWk
trimSub'PresId : (s : Sub' Γ Δ) → trimSub' idWk s ≡ s
trimSub'PresId {Δ = []}     tt         = refl
trimSub'PresId {Δ = Δ `, _} (s , _)    = cong₂ _,_ (trimSub'PresId s) refl
trimSub'PresId {Δ = Δ 🔒}    (lock s e) = cong₂ lock (trimSub'PresId s) refl

-- semantic counterpart of coh-trimSub-wkVar in Substitution.agda
coh-trimSub'-wkVar' : (w : Γ' ≤ Γ) (s : Sub' Δ Γ') (x : Var Γ a)
  → substVar' (wkVar w x) s ≡ substVar' x (trimSub' w s)
coh-trimSub'-wkVar' (drop w) (s , _) ze     = coh-trimSub'-wkVar' w s ze
coh-trimSub'-wkVar' (drop w) (s , _) (su x) = coh-trimSub'-wkVar' w s (su x)
coh-trimSub'-wkVar' (keep w) (s , _) ze     = refl
coh-trimSub'-wkVar' (keep w) (s , _) (su x) = coh-trimSub'-wkVar' w s x

-- semantic counterpart of coh-trimSub-wkTm in HellOfSyntacticLemmas.agda
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

-- 
psh-evalₛ : (s : Sub Γ Γ') (s' : Sub' Δ Γ)
    → Pshₛ s' → Pshₛ (evalₛ s s')
psh-evalₛ []       s' ps'
  = tt
psh-evalₛ (s `, t) s' ps'
  = (psh-evalₛ s s' ps') , (psh-eval t s' ps')
psh-evalₛ (lock s nil) (lock s' e) ps'
  = psh-evalₛ s s' ps'
psh-evalₛ (lock s (ext e)) (s' , _) (ps' , _)
  = psh-evalₛ (lock s e) s' ps'

-- naturality of evalₛ
nat-evalₛ : (w : Δ' ≤ Δ)  (s : Sub Γ' Γ) (s' : Sub' Δ Γ') (ps' : Pshₛ s')
  → evalₛ s (wkSub' w s') ≡ wkSub' w (evalₛ s s')
nat-evalₛ w []               s'        ps'
  = refl
nat-evalₛ w (s `, t)         s'        ps'
  = cong₂ _,_ (nat-evalₛ w s s' ps') (nat-eval t w s' ps')
nat-evalₛ w (lock s (ext e)) (s' , _) (ps' , _)
  = nat-evalₛ w (lock s e) s' ps'
nat-evalₛ w (lock s nil)     (lock s' e) ps'
  = cong₂ lock (nat-evalₛ (sliceLeft e w) s s' ps') refl

-- semantic counterpart of coh-trimSub-wkSub in `HellOfSyntacticLemmas.agda`
coh-trimSub'-wkSub : (w : Γ' ≤ Γ) (s : Sub Γ Δ) (s' : Sub' Δ' Γ')
  → evalₛ (wkSub w s) s' ≡ evalₛ s (trimSub' w s')
coh-trimSub'-wkSub w [] s'
  = refl
coh-trimSub'-wkSub w (s `, t) s'
  = cong₂ _,_ (coh-trimSub'-wkSub w s s') (coh-trimSub'-wkTm w s' t)
coh-trimSub'-wkSub (drop w) (lock s e) (s' , _)
  = coh-trimSub'-wkSub w (lock s e) s'
coh-trimSub'-wkSub (keep w) (lock s (ext e)) (s' , _)
  = coh-trimSub'-wkSub w (lock s e) s'
coh-trimSub'-wkSub (keep🔒 w) (lock s nil) (lock s' e')
  = cong₂ lock (coh-trimSub'-wkSub w s s') refl

evalₛPresId : (s' : Sub' Γ Δ) → evalₛ idₛ s' ≡ s'
evalₛPresId {Δ = []}     tt
  = refl
evalₛPresId {Δ = Δ `, _} (s' , x)
  = cong₂ (_,_)
          (trans
            (coh-trimSub'-wkSub fresh idₛ (s' , x))
            (trans
              (cong (evalₛ idₛ) (trimSub'PresId s'))
              (evalₛPresId s')))
          refl
evalₛPresId {Δ = Δ 🔒} (lock s' e)
  = cong₂ lock (evalₛPresId s') refl


coh-substVar-evalₛ : (x : Var Γ a) (s₀ : Sub Δ Γ) {s s' : Sub' Δ' Δ}
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → substVar' x (evalₛ s₀ s') ≋ eval (substVar s₀ x) s'
coh-substVar-evalₛ ze     (_ `, t) {s} {s'} ps ps' s≋s'
  = pseudo-refl-≋ {x = eval t s'} (sym-≋ {x = eval t s} (fund t ps ps' s≋s'))
coh-substVar-evalₛ (su x) (s₀ `, _) ps ps' s≋s'
  = coh-substVar-evalₛ x s₀ ps ps' s≋s'

coh-substTm-evalₛ : (t : Tm Γ a) (s₀ : Sub Δ Γ) {s s' : Sub' Δ' Δ}
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t (evalₛ s₀ s') ≋ eval (substTm s₀ t) s'  
coh-substTm-evalₛ (var x)     s₀ ps ps' s≋s' 
  = coh-substVar-evalₛ x s₀ ps ps' s≋s'
coh-substTm-evalₛ (lam t)     s₀ {s} {s'} ps ps' s≋s' w {x = x} {y} px py x≋y
  rewrite sym (nat-evalₛ w s₀ s' ps')
  = trans-≋ {z =  eval (substTm (wkSub fresh s₀ `, var ze) t) (wkSub' w s' , y)}
      ((subst (λ z → _ ≋ eval t (z , y))
        (trans
          (cong (evalₛ s₀) (sym (trimSub'PresId _)))
          (sym (coh-trimSub'-wkSub fresh s₀ (wkSub' w s' , y))))
        (fund t
          (psh-evalₛ s₀ _ (wkSub'PresPsh w s' ps') , px)
          (psh-evalₛ s₀ _ (wkSub'PresPsh w s' ps') , py)
          (fundₛ s₀
            (wkSub'PresPsh w s' ps')
            (wkSub'PresPsh w s' ps')
            (wkSub'Pres≋ w ((pseudo-refl-≋ₛ {s = s'} (sym-≋ₛ s≋s')))) `, x≋y))))
      ((coh-substTm-evalₛ t
        (keepₛ s₀)
        (wkSub'PresPsh w s ps , px)
        (wkSub'PresPsh w s' ps' , py)
        (wkSub'Pres≋ w s≋s' `, x≋y)))
coh-substTm-evalₛ (app t u)  s₀ ps ps' s≋s'
  = coh-substTm-evalₛ t s₀ ps ps' s≋s' idWk
      (psh-eval u _ (psh-evalₛ s₀ _ ps'))
      (psh-eval (substTm s₀ u) _ ps')
      (coh-substTm-evalₛ u s₀ ps ps' s≋s')
coh-substTm-evalₛ (box t)     s₀ ps ps' s≋s'
  = coh-substTm-evalₛ t (lock s₀ nil) ps ps' (lock s≋s' nil)
coh-substTm-evalₛ (unbox t (ext e)) (s₀ `, _) ps ps' s≋s'
  = coh-substTm-evalₛ (unbox t e) s₀ ps ps' s≋s'
coh-substTm-evalₛ (unbox t nil) (lock s₀ (ext e)) (ps , _) (ps' , _) (s≋s' `, _)
  = coh-substTm-evalₛ (unbox t nil) (lock s₀ e) ps ps' s≋s'
coh-substTm-evalₛ (unbox t nil) (lock s₀ nil) {s = lock s e} {s' = lock s' e'} ps ps' (lock s≋s' e')
  = unbox'Pres≋ {x = eval t (evalₛ s₀ s')} e' (coh-substTm-evalₛ t s₀ ps ps' s≋s')

private
  lemma1 : {t : Tm (ΓL 🔒) a} (e : LFExt Γ (ΓL 🔒) ΓR) {s s' : Sub' Δ Γ}
    → Pshₛ s → Pshₛ s'
    → s ≋ₛ s'
    → eval (unbox (box t) e) s ≋ eval t (trimSub' (LFExtTo≤ e) s')
  lemma1 {t = t} nil {s = lock s e} {s' = lock s' e} ps ps' (lock s≋s' e)
    with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
  ... | refl | refl
    rewrite sym (nat-eval t (LFExtTo≤ e) (lock s nil) ps)
      | ExtIsProp (wkLFExt nil (LFExtTo≤ e)) e
        = fund t
               (wkSub'PresPsh (sliceLeft nil (LFExtTo≤ e)) s ps)
               (subst Pshₛ (sym (trimSub'PresId s')) ps')
               (lock lemma1-2 e)
    where
      lemma1-1 : ∀ (e : LFExt Γ (←🔒 Γ 🔒) ΓR) → sliceLeft nil (LFExtTo≤ e) ≡ idWk
      lemma1-1 {Γ Context.`, x} (Context.ext e) = lemma1-1 e
      lemma1-1 {Γ Context.🔒} Context.nil = refl
      lemma1-2 : wkSub' (sliceLeft nil (LFExtTo≤ e)) s ≋ₛ trimSub' idWk s'
      lemma1-2 rewrite lemma1-1 e
        | trimSub'PresId s'
        | wkSub'PresId s = s≋s'
  lemma1 {t = t} (ext e) (s  , _) (s' , _) (s≋s' `, _)
    = lemma1 {t = t} e s s' s≋s'
    
  lemma2 : {x y : Tm' Γ (◻ a)}
    → x ≋ y
    → x ≋ box (unbox' y nil)
  lemma2 {x = box x} {box y} x≋y rewrite wkTm'PresId y
      = x≋y

-- soundness of single-step reduction
sound-red : {t t' : Tm Γ a} {s s' : Sub' Δ Γ}
  → t ⟶ t'
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t s ≋ eval t' s'
sound-red {Γ = Γ} {Δ = Δ} {t = app (lam {b = b} t) u} {s = s} {s' = s'} red-fun ps ps' s≋s'
  rewrite wkSub'PresId s
  | evalₛPresId s'
    = trans-≋ {Γ = Δ} {a = b}
      (fund t
            (ps , (psh-eval u s ps))
            (subst Pshₛ (sym (evalₛPresId s')) ps' , psh-eval u s' ps')
            (subst (s ≋ₛ_) (sym (evalₛPresId s')) s≋s' `, fund u ps ps' s≋s'))
      (coh-substTm-evalₛ t (idₛ `, u) {s} {s'} ps ps' s≋s') 
sound-red {t = t} {s = s} {s'} exp-fun  ps ps' s≋s' w {x = x} px py x≋y
  rewrite sym (rightIdWk w)
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
sound-red {t = unbox (box t) e} {s = s} {s' = s'} red-box ps ps' s≋s'
  rewrite coh-trimSub'-wkTm (LFExtTo≤ e) s' t
  = lemma1 {t = t} e ps ps' s≋s'
sound-red {t = t} {s = s} {s'} exp-box ps ps' s≋s'
  = lemma2 {x = eval t s} (fund t ps ps' s≋s')
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
sound-red* {a = a} {t = t} {t' = t'} (r ◅ rs) ps ps' s≋s'
  = trans-≋ {a = a} (sound-red r ps ps' s≋s') (sound-red* rs ps' ps' (pseudo-refl-≋ₛ (sym-≋ₛ s≋s'))) 

-- soundness of conversion
sound-conv : {t t' : Tm Γ a} {s s' : Sub' Δ Γ}
  → t ≈ t'
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t s ≋ eval t' s'
sound-conv {t = t} ε ps ps' s≋s'
  = sound-red* {t = t} (zero refl) ps ps' s≋s'
sound-conv {a = a} (inj₁ r ◅ t≈t') ps ps' s≋s'
  = trans-≋ {a = a} (sound-red r ps ps' s≋s') (sound-conv t≈t' ps' ps' (pseudo-refl-≋ₛ (sym-≋ₛ s≋s')))
sound-conv {a = a} {t = t} {s = s} {s' = s'} (inj₂ r ◅ t≈t') ps ps' s≋s'
  = trans-≋ {a = a}
      (sym-≋ {y = eval t s} (sound-red r ps' ps (sym-≋ₛ s≋s')))
      (sound-conv t≈t' ps' ps' (pseudo-refl-≋ₛ (sym-≋ₛ s≋s')))
