module IS4.Completeness.Trace where

open import Data.Unit
  using (⊤ ; tt)
open import Data.Product
  using (Σ ; _×_ ; _,_ ; ∃)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HE
  using (_≅_)

open import IS4.Term
open import IS4.Reduction
open import IS4.Norm
open import IS4.HellOfSyntacticLemmas

quotTm : Tm' Γ a → Tm Γ a
quotTm x = embNf (reify x)

-----------------------
-- Logical Relations --
-----------------------

Rt : {a : Ty} {Γ : Ctx} → (t : Tm Γ a) → (x : Tm' Γ a) → Set
Rt {𝕓}          t x =
  t ⟶* quotTm x
Rt {a ⇒ b} {Γ}  t f =
  {Γ' : Ctx} {u : Tm Γ' a} {x : Tm' Γ' a}
    → (e : Γ ⊆ Γ') → Rt u x → Rt (app (wkTm e t) u) (f e x)
Rt {◻ a}  {ΓL} t bx =
  {ΓL' Γ ΓR : Ctx}
    → (w : ΓL ⊆ ΓL') → (e : CExt Γ ΓL' ΓR) → Rt (unbox (wkTm w t) e) (bx w e)

data Rs : Sub Γ Δ → Sub' Γ Δ → Set where
  []   : Rs {Γ} [] tt
  _`,_ : {s : Sub Δ Γ} {s' : Sub' Δ Γ} {t : Tm Δ a} {x : Tm' Δ a}
       → Rs s s' → Rt t x → Rs (s `, t)  (s' , x)
  lock : {s : Sub ΔL Γ} {s' : Sub' ΔL Γ}
    → Rs s s' → (e : CExt Δ ΔL (ΔR)) → Rs (lock s e) (lock s' e)

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
  = λ w uRy → Rt-prepend (cong-app* (wkTmPres⟶* w r) (zero refl)) (uRx w uRy)
Rt-prepend {a = ◻ a} {t = t} {u} {x = bx} r uRbx
  = λ w e → Rt-prepend (cong-unbox* (wkTmPres⟶* w r)) (uRbx w e)

-- reduction-free version of Rt-prepend
Rt-cast : {t u : Tm Γ a} {x y : Tm' Γ a}
  → t ≡ u
  → y ≡ x
  → Rt u x
  → Rt t y
Rt-cast p refl uRx = Rt-prepend (zero p) uRx

Rt-hcast : {t u : Tm Γ a} {x y : Tm' Γ a}
  → t ≅ u
  → y ≅ x
  → Rt u x
  → Rt t y
Rt-hcast HE.refl HE.refl uRx = uRx

-- extract reduction trace from Rt
Rt-build : {t : Tm Γ a} {x : Tm' Γ a}
  → Rt t x → t ⟶* quotTm x
-- a neutral element is related to its reflection
Rt-reflect : (n : Ne Γ a)
  → Rt (embNe n) (reflect n)

Rt-build {a = 𝕓}     r
  = r
Rt-build {a = a ⇒ b} tRx
  = multi (one (exp-fun _)) (cong-lam* (Rt-build (tRx _ (Rt-reflect (var ze)))))
Rt-build {a = ◻ a}  tRx
  = multi (one (exp-box _)) (cong-box* (Rt-build (Rt-cast (cong₂ unbox (sym (wkTmPresId _)) refl) refl (tRx idWk new))))

Rt-reflect {a = 𝕓}     n
  = zero refl
Rt-reflect {a = a ⇒ b} n
  = λ w y → Rt-prepend (cong-app* (zero (nat-embNe _ _)) (Rt-build y)) (Rt-reflect _ )
Rt-reflect {a = ◻ a}   n
  = λ w e → Rt-prepend (cong-unbox* (zero (nat-embNe _ _))) (Rt-reflect _)

-- Rt is invariant under weakening
wkTmPresRt : {t : Tm Γ a} {x : Tm' Γ a}
  → (w : Γ ⊆ Δ)
  → Rt t x
  → Rt (wkTm w t) (wkTm' w x)
wkTmPresRt {a = 𝕓}  {x = x}       w tRx
  = multi (wkTmPres⟶* _ tRx) (zero (nat-embNf _ (reify x)))
wkTmPresRt {a = a ⇒ b}            w tRx
  = λ w' y → Rt-cast (cong₂ app (wkTmPres∙ _ _ _) refl) refl (tRx (w ∙ w') y)
wkTmPresRt {a = ◻ a} w tRx
  = λ w' e → Rt-cast (cong₂ unbox (wkTmPres∙ _ _ _) refl) refl (tRx (w ∙ w') e)

-- Rs is invariant under weakening
wkSubPresRs : {s : Sub Δ Γ} {s' : Sub' Δ Γ}
  → (w : Δ ⊆ Δ')
  → Rs s s'
  → Rs (wkSub w s) (wkSub' w s')
wkSubPresRs {Γ = []}     {s = []}      {tt}     w sRs'
  = []
wkSubPresRs {Γ = Γ `, _} {s = s `, t} {s' , x} w (sRs' `, tRx)
  = wkSubPresRs {Γ = Γ} w sRs' `, wkTmPresRt w tRx
wkSubPresRs {Γ = Γ 🔒} {s = lock s e} {lock s' .e} w (lock x .e)
  = lock (wkSubPresRs (factorWk e w) x) (factorExt e w)

-- syntactic identity is related to semantic identity
idRs : Rs {Γ} idₛ idₛ'
idRs {[]}     = []
idRs {Γ `, x} = wkSubPresRs fresh idRs `, Rt-reflect (var ze)
idRs {Γ 🔒}    = lock idRs new

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
    (sym (nat-substTm t (keepₛ s) (keep w)))
    (cong (λ p → substTm (p `, var ze) t)
      (trans
        (wkSubPres∙ (fresh) (keep w) s)
        (cong₂ wkSub (cong drop (leftIdWk w)) refl))))) refl))
    (multi
      (one (red-fun _ _))
      (multi
        (zero (substTmPres∙ _ _ t ))
        (zero (cong (λ p → substTm (p `, u) t) (trans
          (sym (coh-trimSub-wkSub s _ _))
          (trans (coh-trimSub-wkSub s idₛ w) ?))))))

  unboxPresRt : {t : Tm Γ (◻ a)} {x : (Tm'- (◻ a)) Γ}
    → (e : CExt Γ' Γ ΓR)
    → (e' : CExt Γ' Γ ΓR)
    → Rt t x
    → Rt (unbox t e) (unbox' x e')
  unboxPresRt {t = t} {bx} e e' r rewrite ExtIsProp e' e
    = Rt-cast (cong₂ unbox (sym (wkTmPresId t)) refl) refl (r idWk e)

-- The Fundamental theorem, for terms


Fund : Tm Γ a → (Sub'- Γ →̇ Tm'- a) → Set
Fund {Γ} t f = ∀ {Δ} {s : Sub Δ Γ} {s' : Sub' Δ Γ}
    → Rs s s'
    → Rt (substTm s t) (f s')

import Context as C
import IS4.Substitution as S

lCtxₛ'∼lCtxₛ : (e : CExt Γ ΓL ΓR) {s : Sub Δ Γ} {s' : Sub' Δ Γ} → Rs s s' → lCtxₛ' e s' ≡ lCtxₛ e s
lCtxₛ'∼lCtxₛ nil       sRs'          = refl
lCtxₛ'∼lCtxₛ (ext e)   (sRs' `, _)   = lCtxₛ'∼lCtxₛ e sRs'
lCtxₛ'∼lCtxₛ (ext🔒- e) (lock sRs' _) = lCtxₛ'∼lCtxₛ e sRs'

rCtxₛ'∼rCtxₛ : (e : CExt Γ ΓL ΓR) {s : Sub Δ Γ} {s' : Sub' Δ Γ} → Rs s s' →  rCtxₛ' e s' ≡ rCtxₛ e s
rCtxₛ'∼rCtxₛ nil       sRs'          = refl
rCtxₛ'∼rCtxₛ (ext e)   (sRs' `, x)   = rCtxₛ'∼rCtxₛ e sRs'
rCtxₛ'∼rCtxₛ (ext🔒- e) (lock sRs' _) = cong (_,, _) (rCtxₛ'∼rCtxₛ e sRs')

factorSubPresRs : (e : CExt Γ ΓL ΓR) {s : Sub Δ Γ} {s' : Sub' Δ Γ}
    → (sRs' : Rs s s')
    → Rs (factorSubₛ e s) (subst (λ ΔL → Sub' ΔL ΓL) (lCtxₛ'∼lCtxₛ e sRs') (factorSubₛ' e s'))
factorSubPresRs nil       sRs'           = sRs'
factorSubPresRs (ext e)   (sRs' `, _)    = factorSubPresRs e sRs'
factorSubPresRs (ext🔒- e) (lock sRs' _) = factorSubPresRs e sRs'

factorExtₛ'∼factorExtₛ : (e : CExt Γ ΓL ΓR) {s : Sub Δ Γ} {s' : Sub' Δ Γ}
  → (sRs' : Rs s s')
  → factorExtₛ e s ≡ subst₂ (CExt _) (lCtxₛ'∼lCtxₛ e sRs') (rCtxₛ'∼rCtxₛ e sRs') (factorExtₛ' e s')
factorExtₛ'∼factorExtₛ _ _ = ExtIsProp _ _

fund : (t : Tm Γ a) → Fund t (eval t)
fund (var x)     {s = s} {s'} sRs'
  = substVarPresRt x sRs'
fund (lam t)     {s = s} {s'} sRs' {u = u}
  = λ w uRx → Rt-prepend (beta-lemma w s t u)
  (fund t {s = wkSub w s `, u} (wkSubPresRs w sRs' `, uRx))
fund (app t u)   {s = s} {s'} sRs'
  = Rt-cast
      (cong₂ app (sym (wkTmPresId _)) refl)
      refl
      (fund t sRs' idWk (fund u sRs'))
fund {Γ = Γ} (box {a = a} t)    {s = s} {s'} sRs' {Γ = Γ'} {ΓR = ΓR} w e
  = Rt-prepend unbox-box-reduces (fund t (lock (wkSubPresRs w sRs') e))
  where
  unbox-box-reduces : unbox (wkTm w (substTm s (box t))) e ⟶* substTm (lock (wkSub w s) e) t
  unbox-box-reduces = begin
    unbox (wkTm w (substTm s (box t))) e
      ≈⟨⟩
    unbox (box (wkTm (keep🔒 w) (substTm (lock s new) t))) e
      ∼⟨ one (red-box _ _) ⟩
    substTm (lock idₛ e) (wkTm (keep🔒 w) (substTm (lock s new) t))
      ≡⟨ cong (substTm _) (sym (nat-substTm t _ _))  ⟩
    substTm (lock idₛ e) (substTm (wkSub (keep🔒 w) (lock s new)) t)
      ≡⟨ substTmPres∙ _ _ t ⟩
    substTm ((wkSub (keep🔒 w) (lock s new)) ∙ₛ (lock idₛ e) ) t
      ≡⟨⟩
    substTm (lock (wkSub w s ∙ₛ idₛ) (extRAssoc nil e)) t
      ≈⟨ cong (λ s → substTm s t) lemma ⟩
    substTm (lock (wkSub w s) e) t ∎
    where
    open import Relation.Binary.Reasoning.Preorder (Tm-preorder Γ' a)
    lemma : lock (wkSub w s ∙ₛ idₛ) (extRAssoc nil e) ≡ lock (wkSub w s) e
    lemma = {!!} --doable
fund (unbox t e) {s = s} {s'} sRs'
  = Rt-hcast {!!} {!!}
    (fund t
      {s = factorSubₛ e s}
      {s' = subst (λ Δ → Sub' Δ _) (lCtxₛ'∼lCtxₛ e sRs') (factorSubₛ' e s')}
      (factorSubPresRs e sRs')
      {ΓL' = lCtxₛ e s}
      idWk
      (subst₂ (CExt _) (lCtxₛ'∼lCtxₛ e sRs') (rCtxₛ'∼rCtxₛ e sRs') (factorExtₛ' e s')))

-- reduction trace for norm
trace : (t : Tm Γ a) → t ⟶* embNf (norm t)
trace t = Rt-build (Rt-prepend (substTmPresId t) (fund t {s = idₛ} {s' = idₛ'} idRs))
