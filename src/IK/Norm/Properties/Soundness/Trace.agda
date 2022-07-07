{-# OPTIONS --without-K #-}
module IK.Norm.Properties.Soundness.Trace where

open import Data.Unit
  using (⊤ ; tt)
open import Data.Product
  using (Σ ; _×_ ; _,_ ; ∃)

open import Relation.Binary.PropositionalEquality

open import PEUtil

open import IK.Norm.Base

open import IK.Norm.NbE.Model
open import IK.Norm.NbE.Reification

open import IK.Term

quotTm : Tm' Γ a → Tm Γ a
quotTm x = embNf (reify x)

-----------------------
-- Logical Relations --
-----------------------

L : (a : Ty) → (t : Tm Γ a) → (x : Tm' Γ a) → Set
L     ι       t n =
  t ⟶* quotTm n
L {Γ} (a ⇒ b) t f =
  ∀ {Γ' : Ctx} {u : Tm Γ' a} {x : Tm' Γ' a}
    → (w : Γ ⊆ Γ') → (uLx : L a u x) → L b (app (wkTm w t) u) (f w x)
L (□ a)       t b = let box' x = b in
  L a (unbox t new) x

data Lₛ {Γ : Ctx} : (Δ : Ctx) → Sub Γ Δ → Sub' Γ Δ → Set where
  []   : Lₛ [] [] tt
  _`,_ : {s : Sub Γ Δ} {δ : Sub' Γ Δ} {t : Tm Γ a} {x : Tm' Γ a}
           → (sLδ : Lₛ Δ s δ) → (tLx : L a t x) → Lₛ (Δ `, a) (s `, t)  (δ , x)
  lock : {s : Sub Γ' Δ} {δ : Sub' Γ' Δ}
           → (sLδ : Lₛ Δ s δ) → (e : LFExt Γ (Γ' #) ΓR) → Lₛ (Δ #) (lock s e) (lock δ e)

----------------------------
-- Standard LR properties --
----------------------------

-- prepend a reduction trace to the "trace builder" L
L-prepend : {t : Tm Γ a} {x : Tm' Γ a}
  → (t⟶*u : t ⟶* u)
  → (uLx : L a u x)
  → L a t x
L-prepend {a = ι}     t⟶*u uLn
  = multi t⟶*u uLn
L-prepend {a = a ⇒ b} t⟶*u uLf
  = λ w uRy → L-prepend (cong-app1* (wkTmPres⟶* w t⟶*u)) (uLf w uRy)
L-prepend {a = □ a}   t⟶*u uLb
  = L-prepend (cong-unbox* t⟶*u) uLb

-- reduction-free version of L-prepend
L-cast : {t u : Tm Γ a} {x : Tm' Γ a}
  → (t≡u : t ≡ u)
  → (uLx : L a u x)
  → L a t x
L-cast refl uLx = uLx

-- extract reduction trace from L
L-build : {t : Tm Γ a} {x : Tm' Γ a}
  → (tLx : L a t x) → t ⟶* quotTm x
-- a neutral element is related to its reflection
L-reflect : (n : Ne Γ a)
  → L a (embNe n) (reflect n)

L-build {a = ι}     tLn
  = tLn
L-build {a = a ⇒ b} tLf
  = ⟶-multi exp-fun (cong-lam* (L-build (tLf fresh (L-reflect {a = a} var0))))
L-build {a = □ a}   tLb
  = ⟶-multi exp-box (cong-box* (L-build tLb))

L-reflect {a = ι}     n
  = ⟶*-refl
L-reflect {a = a ⇒ b} n {_Γ'} {_t} {x}
  = λ w tLx → L-prepend
                (cong-app≡* (nat-embNe w n) (L-build tLx))
                (L-reflect (app (wkNe w n) (reify x)))
L-reflect {a = □ a}   n
  = L-reflect (unbox n new)

-- L is invariant under weakening
wkTmPresL : {t : Tm Γ a} {x : Tm' Γ a}
  → (w : Γ ⊆ Γ')
  → (tLx : L a t x)
  → L a (wkTm w t) (wkTm' w x)
wkTmPresL {a = ι}     {x = x} w tLn
  = multi-≡ (wkTmPres⟶* w tLn) (nat-embNf w (reify x))
wkTmPresL {a = a ⇒ b} {t = t} w tLf
  = λ w' y → L-cast (cong₂ app (wkTmPres∙ w w' t) refl) (tLf (w ∙ w') y)
wkTmPresL {a = □ a}           w tLb
  = wkTmPresL {a = a} (keep# w) tLb

-- Lₛ is invariant under weakening
wkSubPresLₛ : {s : Sub Γ Δ} {δ : Sub' Γ Δ}
  → (w : Γ ⊆ Γ')
  → (sLδ : Lₛ Δ s δ)
  → Lₛ Δ (wkSub w s) (wkSub' w δ)
wkSubPresLₛ {Δ = []}      w []
  = []
wkSubPresLₛ {Δ = _Δ `, a} w (sLδ `, tLx)
  = wkSubPresLₛ w sLδ `, wkTmPresL {a = a} w tLx
wkSubPresLₛ {Δ = _Δ #}    w (lock sLδ e)
  = lock (wkSubPresLₛ (sliceLeft e w) sLδ) (wkLFExt e w)

-- syntactic identity is related to semantic identity
idLₛ : Lₛ Δ idₛ idₛ'
idLₛ {[]}      = []
idLₛ {_Δ `, a} = wkSubPresLₛ fresh[ a ] idLₛ `, L-reflect {a = a} var0
idLₛ {_Δ #}    = lock idLₛ nil

-----------------------------
-- The Fundamental Theorem --
-----------------------------

-- local lemmas for the proof of fundamental theorem
private
  substVarPresL : (v : Var Δ a) {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (sLδ : Lₛ Δ s δ)
    → L a (substVar s v) (substVar' v δ)
  substVarPresL zero     (_sLδ `, tLx)  = tLx
  substVarPresL (succ v) (sLδ  `, _tLx) = substVarPresL v sLδ

  beta-lemma : (w : Γ ⊆ Γ') (s : Sub Γ Δ) (t : Tm (Δ `, a) b) (u : Tm Γ' a)
    → app (wkTm w (substTm s (lam t))) u ⟶* substTm (wkSub w s `, u) t
  beta-lemma w s t u = ≡-single-≡
    (cong1 app (cong lam (trans
      (sym (nat-subsTm t (keepₛ s) (keep w)))
      (cong (λ p → substTm (p `, var0) t)
        (trans
          (wkSubPres∙ fresh (keep w) s)
          (cong1 wkSub (cong drop (leftIdWk w))))))))
    red-fun
    (trans
      (substTmPres∙ _ _ t )
      (cong (λ p → substTm (p `, u) t) (trans
        (sym (coh-trimSub-wkSub s _ _))
        (trans (coh-trimSub-wkSub s idₛ w) (rightIdSub _)))))

  box-beta-lemma : (t : Tm (Γ #) a) → unbox (box t) new ⟶* t
  box-beta-lemma t = single-≡ red-box (wkTmPresId t)

  module _ {t : Tm Γ (□ a)} {b : Box (Tm'- a) Γ} where
    unboxPresL : (tLb : L (□ a) t b)
      → (e : LFExt Δ (Γ #) ΓR)
      → L a (unbox t e) (unbox' b e)
    unboxPresL tLb e =
      L-cast (unbox-universal t e) (wkTmPresL {a = a} (LFExtToWk e) tLb)

-- The Fundamental theorem, for terms

Fund : Tm Δ a → Set
Fund {Δ} {a} t = ∀ {Γ} {s : Sub Γ Δ} {δ : Sub' Γ Δ}
                   → (sLδ : Lₛ Δ s δ)
                   → L a (substTm s t) (eval t δ)

fund : (t : Tm Δ a) → Fund t
fund (var v)              sLδ
  = substVarPresL v sLδ
fund (lam t)       {_Γ} {s} sLδ {_Γ'} {u}
  = λ w uLx → L-prepend (beta-lemma w s t u)
      (fund t {s = wkSub w s `, u} (wkSubPresLₛ w sLδ `, uLx))
fund (app t u)     {_Γ} {s} sLδ
  = L-cast (cong1 app (sym (wkTmPresId (substTm s t))))
      (fund t sLδ idWk (fund u sLδ))
fund (box t)       {_Γ} {s}        sRδ
  = L-prepend (box-beta-lemma (substTm (keep#ₛ s) t)) (fund t (lock sRδ new))
fund (unbox t nil) {_Γ} {lock s e} (lock sRδ e)
  = unboxPresL {t = substTm s t} (fund t sRδ) e
fund (unbox t (ext e))             (sRδ `, _uRx)
  = fund (unbox t e) sRδ

-- The Fundamental theorem, extended to substitutions
-- (not needed for tracing reduction of terms)

Fundₛ : (S : Sub Δ Θ) → Set
Fundₛ {Δ} {Θ} S = ∀ {Γ} {s : Sub Γ Δ} {δ : Sub' Γ Δ}
                    → (sLδ : Lₛ Δ s δ)
                    → Lₛ Θ (S ∙ₛ s) (evalₛ S δ)

fundₛ : (S : Sub Δ Θ) → Fundₛ S
fundₛ []               sLδ
  = []
fundₛ (S `, t)         sLδ
  = fundₛ S sLδ `, fund t sLδ
fundₛ (lock S nil)     (lock sLδ e)
  = lock (fundₛ S sLδ) e
fundₛ (lock S (ext e)) (sLδ `, _a)
  = fundₛ (lock S e) sLδ

-- reduction trace for norm
trace : (t : Tm Γ a) → t ⟶* embNf (norm t)
trace t = L-build (L-cast (sym (substTmPresId t)) (fund t idLₛ))
