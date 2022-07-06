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

L : (t : Tm Γ a) → (x : Tm' Γ a) → Set
L {a = ι}         t n       =
  t ⟶* quotTm n
L {Γ} {a = a ⇒ b} t f       =
  ∀ {Γ' : Ctx} {u : Tm Γ' a} {x : Tm' Γ' a}
    → (w : Γ ⊆ Γ') → (uLx : L u x) → L (app (wkTm w t) u) (f w x)
L {a = □ a}       t (box x) =
  ∃ λ u → L u x × t ⟶* box u

data Lₛ {Γ : Ctx} : Sub Γ Δ → Sub' Γ Δ → Set where
  []   : Lₛ [] tt
  _`,_ : {s : Sub Γ Δ} {δ : Sub' Γ Δ} {t : Tm Γ a} {x : Tm' Γ a}
           → (sLδ : Lₛ s δ) → (tLx : L t x) → Lₛ (s `, t)  (δ , x)
  lock : {s : Sub Γ' Δ} {δ : Sub' Γ' Δ}
           → (sLδ : Lₛ s δ) → (e : LFExt Γ (Γ' #) ΓR) → Lₛ (lock s e) (lock δ e)

----------------------------
-- Standard LR properties --
----------------------------

-- prepend a reduction trace to the "trace builder" L
L-prepend : {t : Tm Γ a} {x : Tm' Γ a}
  → (t⟶*u : t ⟶* u)
  → (uLx : L u x)
  → L t x
L-prepend {a = ι}                 t⟶*u uLn
  = multi t⟶*u uLn
L-prepend {a = a ⇒ b}             t⟶*u uLf
  = λ w uRy → L-prepend (cong-app1* (wkTmPres⟶* w t⟶*u)) (uLf w uRy)
L-prepend {a = □ a}   {x = box x} t⟶*u (v , vRx , u⟶*bv)
  = v , vRx , multi t⟶*u u⟶*bv

-- reduction-free version of L-prepend
L-cast : {t u : Tm Γ a} {x : Tm' Γ a}
  → (t≡u : t ≡ u)
  → (uLx : L u x)
  → L t x
L-cast refl uLx = uLx

-- extract reduction trace from L
L-build : {t : Tm Γ a} {x : Tm' Γ a}
  → (tLx : L t x) → t ⟶* quotTm x
-- a neutral element is related to its reflection
L-reflect : (n : Ne Γ a)
  → L (embNe n) (reflect n)

L-build {a = ι}                 tLn
  = tLn
L-build {a = a ⇒ b}             tLf
  = ⟶-multi exp-fun (cong-lam* (L-build (tLf fresh (L-reflect (var zero)))))
L-build {a = □ a}   {x = box x} (u , uRx , t⟶*bu)
  = multi t⟶*bu (cong-box* (L-build uRx))

L-reflect {a = ι}     n
  = ⟶*-refl
L-reflect {a = a ⇒ b} n {_Γ'} {_t} {x}
  = λ w y → L-prepend (cong-app≡* (nat-embNe w n) (L-build y)) (L-reflect (app (wkNe w n) (reify x)))
L-reflect {a = □ a}   n
  = unbox (embNe n) nil , L-reflect (unbox n nil) , single exp-box

-- L is invariant under weakening
invL : {t : Tm Γ a} {x : Tm' Γ a}
  → (w : Γ ⊆ Γ')
  → (tLx : L t x)
  → L (wkTm w t) (wkTm' w x)
invL {a = ι}     {x = x}     w tLn =
  multi-≡ (wkTmPres⟶* w tLn) (nat-embNf w (reify x))
invL {a = a ⇒ b} {t = t}     w tLf =
  λ w' y → L-cast (cong₂ app (wkTmPres∙ w w' t) refl) (tLf (w ∙ w') y)
invL {a = □ a}   {x = box x} w (u , uLx , t⟶*bu) =
  wkTm (keep# w) u , invL (keep# w) uLx , wkTmPres⟶* w t⟶*bu

-- Lₛ is invariant under weakening
invLₛ : {s : Sub Γ Δ} {δ : Sub' Γ Δ}
  → (w : Γ ⊆ Γ')
  → (sLδ : Lₛ s δ)
  → Lₛ (wkSub w s) (wkSub' w δ)
invLₛ {Δ = []}       w []           =
  []
invLₛ {Δ = _Δ `, _a} w (sLδ `, tLx) =
  invLₛ w sLδ `, invL w tLx
invLₛ {Δ = _Δ #}     w (lock sLδ e) =
  lock (invLₛ (sliceLeft e w) sLδ) (wkLFExt e w)

-- syntactic identity is related to semantic identity
idLₛ : Lₛ {Δ} idₛ idₛ'
idLₛ {[]}      = []
idLₛ {_Δ `, a} = invLₛ fresh[ a ] idLₛ `, L-reflect {a = a} (var zero)
idLₛ {_Δ #}    = lock idLₛ nil

-----------------------------
-- The Fundamental Theorem --
-----------------------------

-- local lemmas for the proof of fundamental theorem
private
  substVarPresL : (v : Var Δ a) {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (sLδ : Lₛ s δ)
    → L (substVar s v) (substVar' v δ)
  substVarPresL zero     (_sLδ `, tLx)  = tLx
  substVarPresL (succ v) (sLδ  `, _tLx) = substVarPresL v sLδ

  beta-lemma : (w : Γ ⊆ Γ') (s : Sub Γ Δ) (t : Tm (Δ `, a) b) (u : Tm Γ' a)
    → app (wkTm w (substTm s (lam t))) u ⟶* substTm (wkSub w s `, u) t
  beta-lemma w s t u = ≡-single-≡
    (cong1 app (cong lam (trans
      (sym (nat-subsTm t (keepₛ s) (keep w)))
      (cong (λ p → substTm (p `, var zero) t)
        (trans
          (wkSubPres∙ fresh (keep w) s)
          (cong1 wkSub (cong drop (leftIdWk w))))))))
    red-fun
    (trans
      (substTmPres∙ _ _ t )
      (cong (λ p → substTm (p `, u) t) (trans
        (sym (coh-trimSub-wkSub s _ _))
        (trans (coh-trimSub-wkSub s idₛ w) (rightIdSub _)))))

  unboxPresL : {t : Tm Γ (□ a)} {b : Box (Tm'- a) Γ}
    → (e : LFExt Δ (Γ #) ΓR)
    → (tLb : L t b)
    → L (unbox t e) (unbox' b e)
  unboxPresL {b = box x} e (u , uLx , t⟶*bu) =
    L-prepend (multi-⟶ (cong-unbox* t⟶*bu) red-box) (invL (LFExtToWk e) uLx)

-- The Fundamental theorem, for terms

Fund : Tm Δ a → Set
Fund {Δ} t = ∀ {Γ} {s : Sub Γ Δ} {δ : Sub' Γ Δ}
               → (sLδ : Lₛ s δ)
               → L (substTm s t) (eval t δ)

fund : (t : Tm Δ a) → Fund t
fund (var v)              sLδ
  = substVarPresL v sLδ
fund (lam t)     {_Γ} {s} sLδ {_Γ'} {u}
  = λ w uLx → L-prepend (beta-lemma w s t u)
      (fund t {s = wkSub w s `, u} (invLₛ w sLδ `, uLx))
fund (app t u)   {_Γ} {s} sLδ
  = L-cast (cong1 app (sym (wkTmPresId (substTm s t))))
      (fund t sLδ idWk (fund u sLδ))
fund (box t)     {_Γ} {s} sLδ
  = substTm (lock s nil) t , fund t (lock sLδ nil) , ⟶*-refl
fund (unbox t nil)        (lock sLδ e)
  = unboxPresL e (fund t sLδ)
fund (unbox t (ext e))    (sLδ `, _b)
  = fund (unbox t e) sLδ

-- The Fundamental theorem, extended to substitutions
-- (not needed for tracing reduction of terms)

Fundₛ : (S : Sub Δ Θ) → Set
Fundₛ {Δ} S = ∀ {Γ} {s : Sub Γ Δ} {δ : Sub' Γ Δ}
                → (sLδ : Lₛ s δ)
                → Lₛ (S ∙ₛ s) (evalₛ S δ)

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
