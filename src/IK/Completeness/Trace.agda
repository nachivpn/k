{-# OPTIONS --safe --with-K #-}
module IK.Completeness.Trace where

open import Data.Unit
  using (⊤ ; tt)
open import Data.Product
  using (Σ ; _×_ ; _,_ ; ∃)
open import Relation.Binary.PropositionalEquality

open import IK.Term
open import IK.Reduction
open import IK.Norm
open import IK.HellOfSyntacticLemmas

quotTm : Tm' Γ a → Tm Γ a
quotTm x = embNf (reify x)

-----------------------
-- Logical Relations --
-----------------------

Rt : {a : Ty} {Γ : Ctx} → (t : Tm Γ a) → (x : Tm' Γ a) → Set
Rt {𝕓}         t x =
  t ⟶* quotTm x
Rt {a ⇒ b} {Γ} t f =
  {Γ' : Ctx} {u : Tm Γ' a} {x : Tm' Γ' a}
    → (e : Γ ⊆ Γ') → Rt u x → Rt (app (wkTm e t) u) (f e x)
Rt {◻ a}       t (box x) =
  ∃ λ u → Rt u x × t ⟶* box u

data Rs : Sub Γ Δ → Sub' Γ Δ → Set where
  []   : Rs {Γ} [] tt
  _`,_ : {s : Sub Γ Δ} {s' : Sub' Γ Δ} {t : Tm Γ a} {x : Tm' Γ a}
       → Rs s s' → Rt t x → Rs (s `, t)  (s' , x)
  lock : {s : Sub Δ Γ} {s' : Sub' Δ Γ}
    → Rs s s' → (e : LFExt Δ' (Δ 🔒) (ΔR)) → Rs (lock s e) (lock s' e)

----------------------------
-- Standard LR properties --
----------------------------

-- prepend a reduction trace to the "trace builder" Rt
Rt-prepend : {t u : Tm Γ a} {x : Tm' Γ a}
  → t ⟶* u
  → Rt u x
  → Rt t x
Rt-prepend {a = 𝕓} r uRx
  = multi r uRx
Rt-prepend {a = a ⇒ b} r uRx
  = λ w uRy → Rt-prepend (cong-app* (invRed* w r) (zero refl)) (uRx w uRy)
Rt-prepend {a = ◻ a} {t = t} {u} {x = box x} r (t' , t'Rx , r')
  = t' , t'Rx , multi r r'

-- reduction-free version of Rt-prepend
Rt-cast : {t u : Tm Γ a} {x : Tm' Γ a}
  → t ≡ u
  → Rt u x
  → Rt t x
Rt-cast p uRx = Rt-prepend (zero p) uRx

-- extract reduction trace from Rt
Rt-build : {t : Tm Γ a} {x : Tm' Γ a}
  → Rt t x → t ⟶* quotTm x
-- a neutral element is related to its reflection
Rt-reflect : (n : Ne Γ a)
  → Rt (embNe n) (reflect n)

Rt-build {a = 𝕓}                 r
  = r
Rt-build {a = a ⇒ b}             tRx
  = multi (one exp-fun) (cong-lam* (Rt-build (tRx _ (Rt-reflect (var ze)))))
Rt-build {a = ◻ a}   {x = box x} (u , uR- , r)
  = multi r (cong-box* (Rt-build uR-))

Rt-reflect {a = 𝕓}     n
  = zero refl
Rt-reflect {a = a ⇒ b} n
  = λ e y → Rt-prepend (cong-app* (zero (nat-embNe _ _)) (Rt-build y)) (Rt-reflect _ )
Rt-reflect {a = ◻ a}   n
  = unbox (embNe n) nil , Rt-reflect (unbox n nil) , one exp-box

-- Rt is invariant under weakening
invRt : {t : Tm Γ a} {x : Tm' Γ a}
  → (w : Γ ⊆ Δ)
  → Rt t x
  → Rt (wkTm w t) (wkTm' w x)
invRt {a = 𝕓}  {x = x}       w tRx =
  multi (invRed* _ tRx) (zero (nat-embNf _ (reify x)))
invRt {a = a ⇒ b}            w tRx =
  λ w' y → Rt-cast (cong₂ app (wkTmPres∙ _ _ _) refl) (tRx (w ∙ w') y)
invRt {a = ◻ a} {x = box x}  e (u , uRx , r) =
  wkTm (keep🔒 e) u , invRt (keep🔒 e) uRx , invRed* e r

-- Rs is invariant under weakening
invRs : {s : Sub Δ Γ} {s' : Sub' Δ Γ}
  → (w : Δ ⊆ Δ')
  → Rs s s'
  → Rs (wkSub w s) (wkSub' w s')
invRs {Γ = []}     {s = []}      {tt}     w sRs'          =
  []
invRs {Γ = Γ `, _} {s = s `, t} {s' , x} w (sRs' `, tRx)  =
  invRs {Γ = Γ} w sRs' `, invRt w tRx
invRs {Γ = Γ 🔒} {s = lock s e} {lock s' .e} w (lock x .e) =
  lock (invRs (sliceLeft e w) x) (wkLFExt e w)

-- syntactic identity is related to semantic identity
idRs : Rs {Γ} idₛ idₛ'
idRs {[]}     = []
idRs {Γ `, x} = invRs fresh idRs `, Rt-reflect (var ze)
idRs {Γ 🔒}    = lock idRs nil

-----------------------------
-- The Fundamental Theorem --
-----------------------------

-- local lemmas for the proof of fundamental theorem
private

  substVarPresRt : (x : Var Γ a) {s : Sub Δ Γ} {s'  : Sub' Δ Γ}
    → Rs s s'
    → Rt (substVar s x) (substVar' x s')
  substVarPresRt ze {_ `, x} {_ , x'} (_ `, xRx')
    = xRx'
  substVarPresRt (su x) {s `, _} {s' , _} (sRs' `, _)
    = substVarPresRt x sRs'

  beta-lemma : (w : Δ ⊆ Γ')  (s : Sub Δ Γ) (t : Tm (Γ `, a) b) (u : Tm Γ' a)
    → app (wkTm w (substTm s (lam t))) u ⟶* substTm (wkSub w s `, u) t
  beta-lemma w s t u = multi (zero (cong₂ app (cong lam (trans
    (sym (nat-subsTm t (keepₛ s) (keep w)))
    (cong (λ p → substTm (p `, var ze) t)
      (trans
        (wkSubPres∙ (fresh) (keep w) s)
        (cong₂ wkSub (cong drop (leftIdWk w)) refl))))) refl))
    (multi
      (one red-fun)
      (zero (trans
        (substTmPres∙ _ _ t )
        (cong (λ p → substTm (p `, u) t) (trans
          (sym (coh-trimSub-wkSub s _ _))
          (trans (coh-trimSub-wkSub s idₛ w) (rightIdSub _)))))))

  unboxPresRt : {t : Tm Γ (◻ a)} {x : Box (Tm'- a) Γ}
    → (e : LFExt Γ' (Γ 🔒) ΓR)
    → Rt t x
    → Rt (unbox t e) (unbox' x e)
  unboxPresRt {t = t} {box x} e (u , uRx , r) =
    Rt-prepend (multi (cong-unbox* r) (one red-box)) (invRt (LFExtTo⊆ e) uRx)

-- The Fundamental theorem, for terms

Fund : Tm Γ a → (Sub'- Γ →̇ Tm'- a) → Set
Fund {Γ} t f = ∀ {Δ} {s : Sub Δ Γ} {s' : Sub' Δ Γ}
    → Rs s s'
    → Rt (substTm s t) (f s')

fund : (t : Tm Γ a) → Fund t (eval t)
fund (var x)     {s = s} {s'} sRs'
  = substVarPresRt x sRs'
fund (lam t)     {s = s} {s'} sRs' {u = u}
  = λ w uRx → Rt-prepend (beta-lemma w s t u)
  (fund t {s = wkSub w s `, u} (invRs w sRs' `, uRx))
fund (app t u)   {s = s} {s'} sRs'
  = Rt-cast (cong₂ app (sym (wkTmPresId _)) refl)
            (fund t sRs' idWk (fund u sRs'))
fund (box t)     {s = s} {s'} sRs'
  = substTm (lock s nil) t , fund t (lock sRs' nil) , zero refl
fund (unbox t nil) {s = lock s e} {lock s' .e} (lock sRs' .e)
  = unboxPresRt e (fund t sRs')
fund (unbox t (ext e)) {s = s `, _} {s' , _} (sRs' `, _)
  = fund (unbox t e) sRs'

-- The Fundamental theorem, extended to substitutions
-- (not needed for tracing reduction of terms)

Fundₛ : Sub Γ Δ → (Sub'- Γ →̇ Sub'- Δ) → Set
Fundₛ {Γ} s₀ f = ∀ {Δ'} {s : Sub Δ' Γ} {s' : Sub' Δ' Γ}
    → Rs s s'
    → Rs (s₀ ∙ₛ s) (f s')

fundₛ : (s : Sub Γ Δ) → Fundₛ s (evalₛ s)
fundₛ []               sRs'
  = []
fundₛ (s₀ `, t)         sRs'
  = (fundₛ s₀ sRs') `, fund t sRs'
fundₛ (lock s₀ (ext e)) (sRs' `, _)
  = fundₛ (lock s₀ e) sRs'
fundₛ (lock s₀ nil)     (lock sRs' e)
  = lock (fundₛ s₀ sRs') e

-- reduction trace for norm
trace : (t : Tm Γ a) → t ⟶* embNf (norm t)
trace t = Rt-build (Rt-cast (sym (substTmPresId t)) (fund t {s = idₛ} {s' = idₛ'} idRs))
