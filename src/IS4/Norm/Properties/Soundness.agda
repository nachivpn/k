{-# OPTIONS --safe --without-K #-}
module IS4.Norm.Properties.Soundness where

open import Data.Unit    using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_ ; -,_)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; subst ; subst₂ ; cong ; cong₂ ; module ≡-Reasoning)

open import PEUtil

open import IS4.Norm.Base

open import IS4.Norm.NbE.Model       hiding (factorWk)
open import IS4.Norm.NbE.Reification

open import IS4.Term

quotTm : Tm' Γ a → Tm Γ a
quotTm x = embNf (reify _ x)

-----------------------
-- Logical Relations --
-----------------------

L : (a : Ty) → (t : Tm Γ a) → (x : Tm' Γ a) → Set
L     ι       t n =
  t ≈ quotTm n
L {Γ} (a ⇒ b) t f =
  ∀ {Γ' : Ctx} {u : Tm Γ' a} {x : Tm' Γ' a}
    → (w : Γ ⊆ Γ') → (uLx : L a u x) → L b (app (wkTm w t) u) (f .apply w x)
L {Γ} (□ a)   t b =
  ∀ {Γ' Δ ΓR' : Ctx}
    → (w : Γ ⊆ Γ') → (e : CExt Δ Γ' ΓR') → L a (unbox (wkTm w t) e) (b .apply w (-, e))

data Lₛ {Γ : Ctx} : (Δ : Ctx) → Sub Γ Δ → Sub' Γ Δ → Set where
  []   : Lₛ [] [] tt
  _`,_ : {s : Sub Γ Δ} {δ : Sub' Γ Δ} {t : Tm Γ a} {x : Tm' Γ a}
           → (sLδ : Lₛ Δ s δ) → (tLx : L a t x) → Lₛ (Δ `, a) (s `, t) (elem (δ , x))
  lock : {s : Sub Γ' Δ} {δ : Sub' Γ' Δ}
           → (sLδ : Lₛ Δ s δ) → (e : CExt Γ Γ' ΓR') → Lₛ (Δ #) (lock s e) (elem (Γ' , (ΓR' , e) , δ))

----------------------------
-- Standard LR properties --
----------------------------

-- prepend a reduction trace to the "trace builder" L
L-prepend : {t u : Tm Γ a} {x : Tm' Γ a}
  → (t≈u : t ≈ u)
  → (uLx : L a u x)
  → L a t x
L-prepend {a = ι}     t≈u uLn
  = ≈-trans t≈u uLn
L-prepend {a = a ⇒ b} t≈u uLf
  = λ w uRy → L-prepend (cong-app≈ (wkTmPres≈ w t≈u) ≈-refl) (uLf w uRy)
L-prepend {a = □ a}   t≈u uLb
  = λ w e → L-prepend (cong-unbox≈ (wkTmPres≈ w t≈u)) (uLb w e)

-- reduction-free version of L-prepend
L-cast : {t u : Tm Γ a} {x y : Tm' Γ a}
  → (t≡u : t ≡ u)
  → (x≡y : x ≡ y)
  → (uLy : L a u y)
  → L a t x
L-cast refl refl uLy = uLy

-- extract reduction trace from L
L-build : {t : Tm Γ a} {x : Tm' Γ a}
  → (tLx : L a t x) → t ≈ quotTm x
-- a neutral element is related to its reflection
L-reflect : (n : Ne Γ a)
  → L a (embNe n) (reflect a n)

L-build {a = ι}         tLn
  = tLn
L-build {a = a ⇒ b}     tLf
  = ≈-trans
      (⟶-to-≈ (exp-fun _))
      (cong-lam≈ (L-build (tLf fresh[ a ] (L-reflect var0))))
L-build {a = □ a}   {t} tLb
  = ≈-trans
      (⟶-to-≈ (exp-box _))
      (cong-box≈ (L-build (L-cast (cong1- unbox (sym (wkTmPresId t))) refl (tLb idWk new))))

L-reflect {a = ι}     n
  = ≈-refl
L-reflect {a = a ⇒ b} n {_Γ'} {_t} {x}
  = λ w tLx → L-prepend
                (cong-app≈ (≈-reflexive (nat-embNe w n)) (L-build tLx))
                (L-reflect (app (wkNe w n) (reify a x)))
L-reflect {a = □ a}   n
  = λ w e → L-prepend
              (cong-unbox≈ (≈-reflexive (nat-embNe w n)))
              (L-reflect (unbox (wkNe w n) e))

-- L is invariant under weakening
wkTmPresL : {t : Tm Γ a} {x : Tm' Γ a}
  → (w : Γ ⊆ Γ')
  → (tLx : L a t x)
  → L a (wkTm w t) (wkTm' a w x)
wkTmPresL {a = ι}     {x = x} w tLn
  = ≈-trans (wkTmPres≈ w tLn) (≈-reflexive (nat-embNf w (reify ι x)))
wkTmPresL {a = a ⇒ b} {t = t} w tLf
  = λ w' y → L-cast (cong1- app (wkTmPres∙ w w' t)) refl (tLf (w ∙ w') y)
wkTmPresL {a = □ a}   {t = t} w tLb
  = λ w' e → L-cast (cong1- unbox (wkTmPres∙ w w' t)) refl (tLb (w ∙ w') e)

-- Lₛ is invariant under weakening
wkSubPresLₛ : {s : Sub Γ Δ} {δ : Sub' Γ Δ}
  → (w : Γ ⊆ Γ')
  → (sLδ : Lₛ Δ s δ)
  → Lₛ Δ (wkSub w s) (wkSub' Δ w δ)
wkSubPresLₛ {Δ = []}       w []
  = []
wkSubPresLₛ {Δ = _Δ `, _a} w (sLδ `, tLx)
  = wkSubPresLₛ w sLδ `, wkTmPresL w tLx
wkSubPresLₛ {Δ = _Δ #}     w (lock sLδ e)
  = lock (wkSubPresLₛ (factorWk e w) sLδ) (factorExt e w)

-- syntactic identity is related to semantic identity
idLₛ : Lₛ Δ idₛ (idₛ' Δ)
idLₛ {[]}      = []
idLₛ {_Δ `, a} = wkSubPresLₛ fresh[ a ] idLₛ `, L-reflect var0
idLₛ {_Δ #}    = lock idLₛ new

-----------------------------
-- The Fundamental Theorem --
-----------------------------

-- local lemmas for the proof of fundamental theorem
private
  substVarPresL : (v : Var Δ a) {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (sLδ : Lₛ Δ s δ)
    → L a (substVar s v) (substVar' v δ)
  substVarPresL zero     (_sLδ `,  tLx) = tLx
  substVarPresL (succ v) ( sLδ `, _tLx) = substVarPresL v sLδ

  beta-lemma : (w : Γ ⊆ Γ') (s : Sub Γ Δ) (t : Tm (Δ `, a) b) (u : Tm Γ' a)
    → app (wkTm w (substTm s (lam t))) u ≈ substTm (wkSub w s `, u) t
  beta-lemma w s t u = ≈-trans (≈-reflexive (cong1- app (cong lam (trans
    (sym (nat-substTm t (keepₛ s) (keep w)))
    (cong (λ p → substTm (p `, var0) t)
      (trans
        (wkSubPres∙ fresh (keep w) s)
        (cong1- wkSub (cong drop (leftIdWk w)))))))))
    (≈-trans
      (⟶-to-≈ (red-fun _ _))
      (≈-trans
        (≈-reflexive (substTmPres∙ _ _ t))
        (substTmPres≈ t
          (cong-`,≈ₛ
            (≈ₛ-trans
              (≈ₛ-reflexive˘ (coh-trimSub-wkSub s _ _))
              (≈ₛ-trans (≈ₛ-reflexive (coh-trimSub-wkSub s idₛ w)) (≈ₛ-sym (rightIdSub _))))
            ≈-refl))))

  lCtxₛ'∼lCtxₛ : {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (e : CExt Δ ΔL ΔR)
    → (sLδ : Lₛ Δ s δ)
    → lCtxₛ' e δ ≡ lCtxₛ e s
  lCtxₛ'∼lCtxₛ nil       _sLδ           = refl
  lCtxₛ'∼lCtxₛ (ext   e) (sLδ `, _tLx)  = lCtxₛ'∼lCtxₛ e sLδ
  lCtxₛ'∼lCtxₛ (ext#- e) (lock sLδ _e') = lCtxₛ'∼lCtxₛ e sLδ

  rCtxₛ'∼rCtxₛ : {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (e : CExt Δ ΔL ΔR)
    → (sLδ : Lₛ Δ s δ)
    → rCtxₛ' e δ ≡ rCtxₛ e s
  rCtxₛ'∼rCtxₛ nil       _sLδ           = refl
  rCtxₛ'∼rCtxₛ (ext   e) (sLδ `, _tLx)  = rCtxₛ'∼rCtxₛ e sLδ
  rCtxₛ'∼rCtxₛ (ext#- e) (lock sLδ _e') = cong (_,, _) (rCtxₛ'∼rCtxₛ e sLδ)

  factorSubPresLₛ : {s : Sub Γ Δ} {δ : Sub' Γ Δ}
    → (e : CExt Δ ΔL ΔR)
    → (sLδ : Lₛ Δ s δ)
    → Lₛ ΔL (factorSubₛ e s) (subst (λ Γ → Sub' Γ ΔL) (lCtxₛ'∼lCtxₛ e sLδ) (factorSubₛ' e δ))
  factorSubPresLₛ nil       sLδ            = sLδ
  factorSubPresLₛ (ext   e) (sLδ `, _tLx)  = factorSubPresLₛ e sLδ
  factorSubPresLₛ (ext#- e) (lock sLδ _e') = factorSubPresLₛ e sLδ

  module _ (w : Γ ⊆ Γ') (s : Sub Γ Δ) (t : Tm (Δ #) a) (e : CExt Θ Γ' ΓR') where
    unbox-box-reduces : unbox (wkTm w (substTm s (box t))) e ≈ substTm (lock (wkSub w s) e) t
    unbox-box-reduces = begin
      unbox (wkTm w (substTm s (box t))) e
        ≡⟨⟩
      unbox (box (wkTm (keep# w) (substTm (lock s new) t))) e
        ≈⟨ ⟶-to-≈ (red-box _ _) ⟩
      substTm (lock idₛ e) (wkTm (keep# w) (substTm (lock s new) t))
        ≡⟨ cong (substTm _) (sym (nat-substTm t _ _))  ⟩
      substTm (lock idₛ e) (substTm (wkSub (keep# w) (lock s new)) t)
        ≡⟨ substTmPres∙ _ _ t ⟩
      substTm (wkSub (keep# w) (lock s new) ∙ₛ (lock idₛ e) ) t
        ≡⟨⟩
      substTm (lock (wkSub w s ∙ₛ idₛ) (extRAssoc nil e)) t
        ≈˘⟨ substTmPres≈ t (cong-lock≈ₛ′ (rightIdSub (wkSub w s))) ⟩
      substTm (lock (wkSub w s) e) t ∎
      where
        open import Relation.Binary.Reasoning.Setoid (Tm-setoid Θ a)

-- The Fundamental theorem, for terms

Fund : Tm Δ a → Set
Fund {Δ} {a} t = ∀ {Γ} {s : Sub Γ Δ} {δ : Sub' Γ Δ}
                   → (sLδ : Lₛ Δ s δ)
                   → L a (substTm s t) (eval t δ)

fund : (t : Tm Γ a) → Fund t
fund (var v)                       sLδ
  = substVarPresL v sLδ
fund (lam t)          {_Γ} {s}     sLδ {_Γ'} {u}
  = λ w uLx → L-prepend (beta-lemma w s t u)
      (fund t {s = wkSub w s `, u} (wkSubPresLₛ w sLδ `, uLx))
fund (app t u)        {_Γ} {s}     sLδ
  = L-cast
      (cong1- app (sym (wkTmPresId (substTm s t))))
      refl
      (fund t sLδ idWk (fund u sLδ))
fund (box t)          {_Γ} {s}     sLδ
  = λ w e → L-prepend (unbox-box-reduces w s t e) (fund t (lock (wkSubPresLₛ w sLδ) e))
fund (unbox {ΔL} t e) {Γ}  {s} {δ} sLδ
  = L-cast
      (cong-unbox≡′ (sym (wkTmPresId (substTm (factorSubₛ e s) t))))
      (dcong₄ (λ Γ δ w r → eval t {Γ} δ .apply {Γ} w r)
        (lCtxₛ'∼lCtxₛ e sLδ)
        refl
        (subst-application′′ idWk (lCtxₛ'∼lCtxₛ e sLδ))
        (trans (subst-application′ -,_ (lCtxₛ'∼lCtxₛ e sLδ)) (dcong₂ _,_ (rCtxₛ'∼rCtxₛ e sLδ) (ExtIsProp _ _))))
      (fund t
        {s = factorSubₛ e s}
        {δ = subst (λ Δ → Sub' Δ ΔL) (lCtxₛ'∼lCtxₛ e sLδ) (factorSubₛ' e δ)}
        (factorSubPresLₛ e sLδ)
        idWk[ lCtxₛ e s ]
        (subst₂ (CExt Γ) (lCtxₛ'∼lCtxₛ e sLδ) (rCtxₛ'∼rCtxₛ e sLδ) (factorExtₛ' e δ)))

-- reduction trace for norm
trace : (t : Tm Γ a) → t ≈ embNf (norm t)
trace t = L-build (L-prepend (substTmPresId t) (fund t idLₛ))

norm-sound : norm t ≡ norm u → t ≈ u
norm-sound {t = t} {u} t'≡u' = ≈-trans (trace t) (≡-≈-trans˘ (cong embNf t'≡u') (trace u))
