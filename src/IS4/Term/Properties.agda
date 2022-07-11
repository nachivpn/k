{-# OPTIONS --safe --with-K #-}
module IS4.Term.Properties where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; subst ; subst₂ ; subst-subst ; module ≡-Reasoning)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import HEUtil
open import PEUtil renaming (˘trans to ≡-˘trans)
import RUtil

open import IS4.Term.Base
open import IS4.Term.Conversion
open import IS4.Term.Reduction

----------------------
-- Substitution lemmas
----------------------

-- Left context of weakening and applying a substituion
-- is the same as the
-- Left context of applying and then weakening it
lCtxₛ-wkSub-comm : (e  : CExt Γ ΓL ΓR) (w  : Δ ⊆ Δ') (s  : Sub Δ Γ)
  → lCtxₛ e (wkSub w s) ≡ lCtx (factorExtₛ e s) w
lCtxₛ-wkSub-comm nil       w s           = ≡-refl
lCtxₛ-wkSub-comm (ext e)   w (s `, _)    = lCtxₛ-wkSub-comm e w s
lCtxₛ-wkSub-comm (ext#- e) w (lock s e') = ≡-trans
  (lCtxₛ-wkSub-comm e (factorWk e' w) s)
  (≡-sym (lCtxPresTrans (factorExtₛ e _) e' _))

-- Right context of weakening and applying a substituion
-- is the same as the
-- Right context of applying and then weakening it
rCtxₛ-wkSub-comm : (e  : CExt Γ ΓL ΓR) (w  : Δ ⊆ Δ') (s  : Sub Δ Γ)
  → rCtxₛ e (wkSub w s) ≡ rCtx (factorExtₛ e s) w
rCtxₛ-wkSub-comm nil w s                 = ≡-refl
rCtxₛ-wkSub-comm (ext e) w (s `, _)      = rCtxₛ-wkSub-comm e w s
rCtxₛ-wkSub-comm (ext#- e) w (lock s e') = ≡-trans
  (cong₂ _,,_ (rCtxₛ-wkSub-comm e (factorWk e' w) s) ≡-refl)
  (≡-sym (rCtxPresTrans (factorExtₛ e _) e' _))

-- Weakening and factoring a subtitution can be achieved by factoring and then weakening it
factorSubₛ-wkSub-comm : (e :  CExt Γ ΓL ΓR) (s  : Sub Δ Γ) (w : Δ ⊆ Δ')
  → subst (λ ΔL → Sub ΔL ΓL) (lCtxₛ-wkSub-comm e w s) (factorSubₛ e (wkSub w s)) ≡ wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)
factorSubₛ-wkSub-comm nil       s           w = ≡-refl
factorSubₛ-wkSub-comm (ext e)   (s `, t)    w = factorSubₛ-wkSub-comm e s w
factorSubₛ-wkSub-comm (ext#- e) (lock s e') w = let open ≡-Reasoning in begin
  subst (λ ΔL → Sub ΔL _)
    (≡-trans (lCtxₛ-wkSub-comm e _ _) (≡-sym (lCtxPresTrans _ e' _)))
    (factorSubₛ e (wkSub (factorWk e' w) s))
    -- split `subst _ (trans p q) ...` to `subst _ q (subst _ p ...)`
    ≡⟨ ≡-sym (subst-subst (lCtxₛ-wkSub-comm e _ _)) ⟩
  subst (λ ΔL → Sub ΔL _)
    (≡-sym (lCtxPresTrans _ e' _))
    (subst (λ ΔL → Sub ΔL _) (lCtxₛ-wkSub-comm e _ _)
      (factorSubₛ e (wkSub (factorWk e' w) s)))
    -- rewrite inner subst
    ≡⟨ cong (subst (λ ΔL → Sub ΔL _) _) (factorSubₛ-wkSub-comm e s (factorWk e' w)) ⟩
  subst (λ ΔL → Sub ΔL _)
    (≡-sym (lCtxPresTrans _ e' _))
    (wkSub (factorWk (factorExtₛ e s) (factorWk e' w)) (factorSubₛ e s))
    -- remove subst and apply factorWkPresTrans
    ≅⟨ ≅-trans (≡-subst-removable _ _ _) factorWkPresTrans-under-wkSub ⟩
 wkSub (factorWk (extRAssoc (factorExtₛ e s) e') w) (factorSubₛ e s) ∎
 where
   factorWkPresTrans-under-wkSub : wkSub (factorWk (factorExtₛ e s) (factorWk e' w)) _ ≅ wkSub (factorWk (extRAssoc (factorExtₛ e s) e') w) _
   factorWkPresTrans-under-wkSub = ≅-cong (_ ⊆_) (≡-sym (lCtxPresTrans _ e' _)) (λ s' → wkSub s' _)
     (≅-sym (≅-trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresTrans _ e' _))))

-- factorExtₛ counterpart of factorSubₛ-wkSub-comm
factorExtₛ-wkSub-comm : (e :  CExt Γ ΓL ΓR) (s  : Sub Δ Γ) (w : Δ ⊆ Δ')
  → subst₂ (CExt Δ') (lCtxₛ-wkSub-comm e w s) (rCtxₛ-wkSub-comm e w s) (factorExtₛ e (wkSub w s)) ≡ factorExt (factorExtₛ e s) w
factorExtₛ-wkSub-comm _ _ _ = ExtIsProp _ _

lCtxₛ-factorExt-trimSub-assoc : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
   → lCtxₛ e (trimSub w s) ≡ lCtxₛ (factorExt e w) s
lCtxₛ-factorExt-trimSub-assoc nil       s          w
  = ≡-refl
lCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, _)   (drop w)
  = lCtxₛ-factorExt-trimSub-assoc (ext e) s w
lCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, _)   (keep w)
  = lCtxₛ-factorExt-trimSub-assoc e s w
lCtxₛ-factorExt-trimSub-assoc (ext#- e) (s `, t)   (drop w)
  = lCtxₛ-factorExt-trimSub-assoc (ext#- e) s w
lCtxₛ-factorExt-trimSub-assoc (ext#- e) (lock s _) (keep# w)
  = lCtxₛ-factorExt-trimSub-assoc e s w

rCtxₛ-factorExt-trimSub-assoc : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
   → rCtxₛ e (trimSub w s) ≡ rCtxₛ (factorExt e w) s
rCtxₛ-factorExt-trimSub-assoc nil       s          w
  = ≡-refl
rCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, t)   (drop w)
  = rCtxₛ-factorExt-trimSub-assoc (ext e) s w
rCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, t)   (keep w)
  = rCtxₛ-factorExt-trimSub-assoc e s w
rCtxₛ-factorExt-trimSub-assoc (ext#- e) (s `, t)   (drop w)
  = rCtxₛ-factorExt-trimSub-assoc (ext#- e) s w
rCtxₛ-factorExt-trimSub-assoc (ext#- e) (lock s _) (keep# w)
  = cong (_,, _) (rCtxₛ-factorExt-trimSub-assoc e s w)

factorSubₛ-trimSub-comm : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → subst (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s w) (factorSubₛ e (trimSub w s)) ≡ trimSub (factorWk e w) (factorSubₛ (factorExt e w) s)
factorSubₛ-trimSub-comm nil       s          w
  = ≡-refl
factorSubₛ-trimSub-comm (ext e)   (s `, _)   (drop w)
  = factorSubₛ-trimSub-comm (ext e) s w
factorSubₛ-trimSub-comm (ext e)   (s `, _)   (keep w)
  = factorSubₛ-trimSub-comm e s w
factorSubₛ-trimSub-comm (ext#- e) (s `, t)   (drop w)
  = factorSubₛ-trimSub-comm (ext#- e) s w
factorSubₛ-trimSub-comm (ext#- e) (lock s _) (keep# w)
  = factorSubₛ-trimSub-comm e s w

factorExtₛ-trimSub-comm : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → subst₂ (CExt Δ') (lCtxₛ-factorExt-trimSub-assoc e s w) (rCtxₛ-factorExt-trimSub-assoc e s w) (factorExtₛ e (trimSub w s)) ≡ factorExtₛ (factorExt e w) s
factorExtₛ-trimSub-comm _ _ _ = ExtIsProp _ _

---------------------------------------------
-- Factorisation of the identity substitution
---------------------------------------------

←#₁rCtx : (e : CExt Γ ΓL ΓR) → Ctx
←#₁rCtx nil             = []
←#₁rCtx (ext {a = a} e) = ←#₁rCtx e ,, rCtx′ (factorExtₛ e idₛ) freshExt[ a ]
←#₁rCtx (ext#- e)       = ←#₁rCtx e

private

  ex : {a b c : Ty} → CExt (ΓL `, a `, b # `, c #) ΓL ([] `, a `, b # `, c #)
  ex {Γ} {a} {b} {c} = ext#- (ext[ c ] (ext#- (ext[ b ] (ext[ a ] nil))))

  _ : ←#₁rCtx (ex {ΓL} {c = c}) ≡ [] `, a `, b
  _ = ≡-refl

-- Given `e` that ΓL extends Γ, ΓL is a lock-free extension of `lCtxₛ e idₛ`.
-- This means that ΓL ⊆ (lCtxₛ e idₛ), and thus applying `factorSubₛ e idₛ` weakens
-- a term with variables in `←#₁rCtx e`
factorSubₛIdWk : (e : CExt Γ ΓL ΓR) → LFExt (lCtxₛ e idₛ) ΓL (←#₁rCtx e)
factorSubₛIdWk                nil              = nil
factorSubₛIdWk {ΓR = ΓR `, a} (ext {a = .a} e) = subst
  (λ Γ → LFExt Γ _ (←#₁rCtx (ext e))) (≡-sym ((lCtxₛ-wkSub-comm e fresh idₛ)))
  (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))
factorSubₛIdWk                (ext#- e)        = factorSubₛIdWk e

-- Obs: Deliberately named _Wk instead of _LFExt

--------------------
-- Substitution laws
--------------------

-- NOTE: these are only the laws that follow directly from the structure of substitutions
coh-trimSub-wkVar : (x : Var Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substVar (trimSub w s) x ≡ substVar s (wkVar w x)
coh-trimSub-wkVar zero (s `, x) (drop w)
  = coh-trimSub-wkVar zero s w
coh-trimSub-wkVar zero (s `, x) (keep w)
  = ≡-refl
coh-trimSub-wkVar (succ x) (s `, x₁) (drop w)
  = coh-trimSub-wkVar (succ x) s w
coh-trimSub-wkVar (succ x) (s `, x₁) (keep w)
  = coh-trimSub-wkVar x s w

-- `trimSub` preserves the identity
trimSubPresId : (s : Sub Δ Γ) → trimSub idWk s ≡ s
trimSubPresId []         = ≡-refl
trimSubPresId (s `, x)   = cong (_`, _) (trimSubPresId s)
trimSubPresId (lock s x) = cong₂ lock (trimSubPresId s) ≡-refl

-- naturality of substVar
nat-substVar : (x : Var Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substVar (wkSub w s) x ≡ wkTm w (substVar s x)
nat-substVar zero     (s `, t) w = ≡-refl
nat-substVar (succ x) (s `, t) w = nat-substVar x s w

-- naturality of trimSub
nat-trimSub : (s : Sub Γ Δ) (w : Δ' ⊆ Δ) (w' : Γ ⊆ Γ')
  → wkSub w' (trimSub w s) ≡ trimSub w (wkSub w' s)
nat-trimSub []         base      w' = ≡-refl
nat-trimSub (s `, t)   (drop w)  w' = nat-trimSub s w w'
nat-trimSub (s `, t)   (keep w)  w' = cong (_`, wkTm w' t) (nat-trimSub s w w')
nat-trimSub (lock s x) (keep# w) w' = cong₂ lock (nat-trimSub s w _) ≡-refl

-- `trimSub` on the identity substitution embeds the weakening
trimSubId : (w : Γ ⊆ Δ) → trimSub w idₛ ≡ embWk w
trimSubId base      = ≡-refl
trimSubId (drop w)  = ≡-trans
  (≡-sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w))
trimSubId (keep w)  = cong (_`, var zero) (≡-trans
  (≡-sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w)))
trimSubId (keep# w) = cong₂ lock (trimSubId w) ≡-refl

---------------------------
-- Hell Of Syntactic Lemmas
---------------------------

-- Welcome to the hell of mind-numbing syntactic lemmas.
-- No good ever comes from proving these lemmas, but no
-- good can happen without proving them.

cong-unbox≅ : {ΓL1 ΓL2 ΓR1 ΓR2 : Ctx} →
           ΓL1 ≡ ΓL2 → ΓR1 ≡ ΓR2 →
          {t1 : Tm ΓL1 (□ a)} {t2 : Tm ΓL2 (□ a)} {e1 : CExt Γ ΓL1 ΓR1} {e2 : CExt Γ ΓL2 ΓR2} →
          t1 ≅ t2 →
          e1 ≅ e2 →
          unbox t1 e1 ≅ unbox t2 e2
cong-unbox≅ {Γ = Γ} ΓL1≡ΓL2 ΓR1≡ΓR2 t1≅t2 e1≅e2
  = xcong (λ ΓL → Tm ΓL _) (CExt Γ) {R = λ _ _ → Tm Γ _} ΓL1≡ΓL2 ΓR1≡ΓR2 unbox t1≅t2 e1≅e2

cong-lock≅ : {ΓL1 ΓL2 ΓR1 ΓR2 : Ctx} →
           ΓL1 ≡ ΓL2 → ΓR1 ≡ ΓR2 →
          {s1 : Sub ΓL1 Δ} {s2 : Sub ΓL2 Δ} {e1 : CExt Γ ΓL1 ΓR1} {e2 : CExt Γ ΓL2 ΓR2} →
          s1 ≅ s2 →
          e1 ≅ e2 →
          lock s1 e1 ≅ lock s2 e2
cong-lock≅ {Γ = Γ} ΓL1≡ΓL2 ΓR1≡ΓR2 s1≅s2 e1≅e2
  = xcong (λ ΓL → Sub ΓL _) (CExt Γ) {R = λ _ _ → Sub Γ _} ΓL1≡ΓL2 ΓR1≡ΓR2 lock s1≅s2 e1≅e2

wkTmPresId : (t : Tm Γ a) → wkTm idWk t ≡ t
wkTmPresId (var x)     = cong var (wkVarPresId x)
wkTmPresId (lam t)     = cong lam (wkTmPresId t)
wkTmPresId (app t u)   = cong₂ app (wkTmPresId t) (wkTmPresId u)
wkTmPresId (box t)     = cong box (wkTmPresId t)
wkTmPresId {Γ = Γ} {a = a} (unbox {ΓL = ΓL} {ΓR = ΓR} t e) = let open ≡-Reasoning in begin
  wkTm idWk (unbox t e)
    ≡⟨⟩
  unbox {ΓL = lCtx e idWk} {ΓR = rCtx e idWk} (wkTm (factorWk e idWk[ Γ ]) t) (factorExt e idWk[ Γ ])
    ≅⟨ xcong
      (λ ΓL → Tm ΓL (□ a)) (CExt Γ)
      (lCtxPresId e) (rCtxPresId e)
      unbox
      factorWkPresId-under-wkTm
      (≡-subst₂-addable (CExt Γ) _ _ (factorExt _ _)) ⟩
  unbox {ΓL = ΓL} {ΓR = ΓR} (wkTm idWk[ ΓL ] t) (subst₂ (CExt Γ) (lCtxPresId e) (rCtxPresId e) (factorExt e idWk))
    ≡⟨ cong₂ unbox (wkTmPresId t) (factorExtPresId e) ⟩
  unbox t e ∎
    where
      factorWkPresId-under-wkTm : wkTm (factorWk e idWk) t ≅ wkTm idWk t
      factorWkPresId-under-wkTm = ≅-cong (ΓL ⊆_) (lCtxPresId e) (λ w → wkTm w t)
        (≅-trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresId e)))

wkSubPresId : (s : Sub Δ Γ) → wkSub idWk s ≡ s
wkSubPresId []         = ≡-refl
wkSubPresId (s `, t)   = cong₂ _`,_ (wkSubPresId s) (wkTmPresId t)
wkSubPresId {Δ = Δ} (lock {ΔL = ΔL} {Γ = Γ} s e) = let open ≡-Reasoning in begin
  wkSub idWk (lock s e)
    ≡⟨⟩
  lock (wkSub (factorWk e idWk) s) (factorExt e idWk)
    ≅⟨ xcong
      (λ ΔL → Sub ΔL Γ) (CExt Δ)
      (lCtxPresId e) (rCtxPresId e)
      lock
      factorWkPresId-under-wkSub
      (≡-subst₂-addable (CExt Δ) _ _ (factorExt _ _)) ⟩
  lock (wkSub idWk s) (subst₂ (CExt Δ) (lCtxPresId e) (rCtxPresId e) (factorExt e idWk))
    ≡⟨ cong₂ lock (wkSubPresId s) (factorExtPresId e) ⟩
  lock s e ∎
    where
      factorWkPresId-under-wkSub : wkSub (factorWk e idWk) s ≅ wkSub idWk s
      factorWkPresId-under-wkSub = ≅-cong (ΔL ⊆_) (lCtxPresId e) (λ w → wkSub w s)
        (≅-trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresId e)))

wkTmPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (t : Tm Γ a)
  → wkTm w' (wkTm w t) ≡ wkTm (w ∙ w') t
wkTmPres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkTmPres∙ w w' (lam t)     = cong lam (wkTmPres∙ (keep w) (keep w') t)
wkTmPres∙ w w' (app t u)   = cong₂ app (wkTmPres∙ w w' t) (wkTmPres∙ w w' u)
wkTmPres∙ w w' (box t)     = cong box (wkTmPres∙ (keep# w) (keep# w') t)
wkTmPres∙ {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} w w' (unbox {ΓL = ΓL} {a = a} {ΓR = ΓR} t e) = let open ≡-Reasoning in begin
  wkTm w' (wkTm w (unbox t e))
    ≡⟨⟩
  unbox {ΓL = lCtx (factorExt e w) w'} {ΓR = rCtx (factorExt e w) w'}
    (wkTm (factorWk (factorExt e w) w') (wkTm (factorWk e w) t))
    (factorExt (factorExt e w) w')
    ≡⟨ cong₂ unbox (wkTmPres∙ _ _ t) (≡-sym (factorExtPres∙ _ _ _)) ⟩
  unbox {ΓL = lCtx (factorExt e w) w'} {ΓR = rCtx (factorExt e w) w'}
    (wkTm (factorWk e w ∙ factorWk (factorExt e w) w') t)
    (subst₂ (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')))
    ≅⟨ xcong
      (λ ΓL → Tm ΓL (□ a)) (CExt Γ'')
      (≡-sym (lCtxPres∙ e w w')) (≡-sym (rCtxPres∙ e w w'))
      unbox
      factorWkPres∙-under-wkTm
      (≡-subst₂-removable (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w'))) ⟩
  unbox {ΓL = lCtx e (w ∙ w')} {ΓR = rCtx e (w ∙ w')} (wkTm (factorWk e (w ∙ w')) t) (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkTm (w ∙ w') (unbox t e) ∎
    where
      factorWkPres∙-under-wkTm :  wkTm (factorWk e w ∙ factorWk (factorExt e w) w') t ≅ wkTm (factorWk e (w ∙ w')) t
      factorWkPres∙-under-wkTm = ≅-cong (ΓL ⊆_) (≡-sym (lCtxPres∙ e w w')) (λ w → wkTm w t)
        (≅-trans (≡-to-≅ (≡-sym (factorWkPres∙ e w w'))) (≡-subst-removable _ _ _))

wkSubPres∙ : (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') (s : Sub Δ Γ)
  → wkSub w' (wkSub w s) ≡ wkSub (w ∙ w') s
wkSubPres∙ w w' []         = ≡-refl
wkSubPres∙ w w' (s `, t)   = cong₂ _`,_ (wkSubPres∙ w w' s) (wkTmPres∙ w w' t)
wkSubPres∙ {Δ'' = Δ''} w w' (lock {ΔL = ΔL} {Γ = Γ} s e) = let open ≡-Reasoning in begin
  wkSub w' (wkSub w (lock s e))
    ≡⟨⟩
  lock (wkSub (factorWk (factorExt e w) w') (wkSub (factorWk e w) s)) (factorExt (factorExt e w) w')
    ≡⟨ cong₂ lock (wkSubPres∙ _ _ _ ) (≡-sym (factorExtPres∙ _ _ _)) ⟩
  lock
    (wkSub (factorWk e w ∙ factorWk (factorExt e w) w') s)
    (subst₂ (CExt Δ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')))
    ≅⟨ xcong
      (λ ΔL → Sub ΔL Γ) (CExt Δ'')
      (≡-sym (lCtxPres∙ e w w')) (≡-sym (rCtxPres∙ e w w'))
      lock
      factorWkPres∙-under-wkSub
      (≡-subst₂-removable (CExt Δ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w'))) ⟩
  lock (wkSub (factorWk e (w ∙ w')) s) (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkSub (w ∙ w') (lock s e) ∎
    where
      factorWkPres∙-under-wkSub :  wkSub (factorWk e w ∙ factorWk (factorExt e w) w') s ≅ wkSub (factorWk e (w ∙ w')) s
      factorWkPres∙-under-wkSub = ≅-cong (ΔL ⊆_) (≡-sym (lCtxPres∙ e w w')) (λ w → wkSub w s)
        (≅-trans (≡-to-≅ (≡-sym (factorWkPres∙ e w w'))) (≡-subst-removable _ _ _))

private
  wkSubFreshLemma : {s : Sub Δ Γ} {w : Δ ⊆ Δ'}
    → wkSub fresh[ a ] (wkSub w s) ≡ wkSub (keep w) (dropₛ s)
  wkSubFreshLemma {s = s} {w} = ≡-trans (wkSubPres∙ w fresh s) (≡-trans
    (cong₂ wkSub (cong drop (rightIdWk _)) ≡-refl )
    (≡-sym (≡-trans
      (wkSubPres∙ _ _ _)
      (cong₂ wkSub (cong drop (leftIdWk _)) ≡-refl))))

nat-substTm : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
nat-substTm (var x)           s          w
  = nat-substVar x s w
nat-substTm (lam {Γ} {a} t)   s          w
  = cong lam
    (≡-trans (cong (λ s → substTm (s `, var zero) t) wkSubFreshLemma)
    (nat-substTm t (keepₛ s) (keep w)))
nat-substTm (app t u)         s          w
  = cong₂ app (nat-substTm t s w) (nat-substTm u s w)
nat-substTm (box t)           s          w
  = cong box (nat-substTm t (lock s (ext#- nil)) (keep# w))
nat-substTm {Γ = Γ} {Δ' = Δ'} (unbox {ΓL = ΓL} {a = a} t e) s w
  = let open ≡-Reasoning in begin
      substTm (wkSub w s) (unbox t e)
        ≡⟨⟩
      unbox {ΓL = lCtxₛ e (wkSub w s)} {ΓR = rCtxₛ e (wkSub w s)}
        (substTm (factorSubₛ e (wkSub w s)) t)
        (factorExtₛ e (wkSub w s))
        ≅⟨ xcong
          (λ ΓL →  Tm ΓL (□ a)) (CExt Δ')
          (lCtxₛ-wkSub-comm e w s) (rCtxₛ-wkSub-comm e w s)
          unbox
          factorSubₛ-wkSub-comm-under-substTm
          (≡-subst₂-addable (CExt Δ') (lCtxₛ-wkSub-comm e w s) _ _) ⟩
     unbox {ΓL = lCtx (factorExtₛ e s) w} {ΓR = rCtx (factorExtₛ e s) w}
        (substTm (wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)) t)
        (subst₂ (CExt Δ') (lCtxₛ-wkSub-comm e w s) (rCtxₛ-wkSub-comm e w s) (factorExtₛ e (wkSub w s)))
        ≡⟨ cong₂ unbox (nat-substTm t _ _) (factorExtₛ-wkSub-comm e s _) ⟩
      unbox {ΓL = lCtx (factorExtₛ e s) w} {ΓR = rCtx (factorExtₛ e s) w}
        (wkTm (factorWk (factorExtₛ e s) w) (substTm (factorSubₛ e s) t))
        (factorExt (factorExtₛ e s) w)
        ≡⟨⟩
      wkTm w (substTm s (unbox t e)) ∎
      where
        factorSubₛ-wkSub-comm-under-substTm : substTm (factorSubₛ e (wkSub w s)) t ≅ substTm (wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)) t
        factorSubₛ-wkSub-comm-under-substTm = ≅-cong (λ x → Sub x ΓL) (lCtxₛ-wkSub-comm e w s) (λ z → substTm z t)
          (≅-trans (≡-subst-addable _ _ _) (≡-to-≅ (factorSubₛ-wkSub-comm e s w)))

coh-wkSub-∙ₛ  : {Δ'' : Ctx} (s : Sub Δ Γ) (s' : Sub Δ' Δ) (w : Δ' ⊆ Δ'')
         → wkSub w (s ∙ₛ s') ≡ s ∙ₛ (wkSub w s')
coh-wkSub-∙ₛ []         s' w = ≡-refl
coh-wkSub-∙ₛ (s `, x)   s' w = cong₂ _`,_  (coh-wkSub-∙ₛ s s' w) (≡-sym (nat-substTm x s' w))
coh-wkSub-∙ₛ (lock s e) s' w = let open ≡-Reasoning in begin
  wkSub w (lock s e ∙ₛ s')
    ≡⟨⟩
  lock
    (wkSub (factorWk (factorExtₛ e s') w) (s ∙ₛ factorSubₛ e s'))
    (factorExt (factorExtₛ e s') w)
    -- apply IH
    ≡⟨ cong₂ lock (coh-wkSub-∙ₛ _ _ _) ≡-refl ⟩
 lock
   (s ∙ₛ wkSub (factorWk (factorExtₛ e s') w) (factorSubₛ e s'))
   (factorExt (factorExtₛ e s') w)
   -- applying factoring equalities
   ≡⟨ cong₂ lock (cong (_ ∙ₛ_) (≡-sym (factorSubₛ-wkSub-comm e s' w))) (≡-sym (factorExtₛ-wkSub-comm e _ _)) ⟩
 lock
   (s ∙ₛ subst (λ ΔL → Sub ΔL _) (lCtxₛ-wkSub-comm e w s') (factorSubₛ e (wkSub w s')))
   (subst₂ (CExt _) (lCtxₛ-wkSub-comm e w s') (rCtxₛ-wkSub-comm e w s') (factorExtₛ e (wkSub w s')))
   -- remove substs
   ≅⟨ xcong
     (λ ΓL → Sub ΓL _) (CExt _)
     (≡-sym (lCtxₛ-wkSub-comm e w s')) (≡-sym (rCtxₛ-wkSub-comm e w s'))
     {t2 = s ∙ₛ factorSubₛ e (wkSub w s')}
     {e2 = factorExtₛ e (wkSub w s')}
     lock
     (≅-cong  (λ ΔL → Sub ΔL _) (≡-sym (lCtxₛ-wkSub-comm e w s')) (s ∙ₛ_) (≡-subst-removable _ _ _))
     (≡-subst₂-removable _ _ _ _) ⟩
 lock
   (s ∙ₛ factorSubₛ e (wkSub w s'))
   (factorExtₛ e (wkSub w s'))
   ≡⟨⟩
 lock s e ∙ₛ wkSub w s' ∎

coh-trimSub-wkTm : (t : Tm Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substTm (trimSub w s) t ≡ substTm s (wkTm w t)
coh-trimSub-wkTm (var x) s w
  = coh-trimSub-wkVar x s w
coh-trimSub-wkTm (lam t) s w
  = cong lam (≡-trans
    (cong (λ p → substTm (p `, var zero) t) (nat-trimSub s w fresh))
    (coh-trimSub-wkTm t (keepₛ s) (keep w)))
coh-trimSub-wkTm (app t u) s w
  = cong₂ app (coh-trimSub-wkTm t s w) (coh-trimSub-wkTm u s w)
coh-trimSub-wkTm (box t) s w
  = cong box (coh-trimSub-wkTm t (lock s (ext#- nil)) (keep# w))
coh-trimSub-wkTm (unbox t e) s w
  = let open ≡-Reasoning in begin
    substTm (trimSub w s) (unbox t e)
      ≡⟨⟩
    unbox
      (substTm (factorSubₛ e (trimSub w s)) t)
      (factorExtₛ e (trimSub w s))
      -- add substs
      ≅⟨ xcong (λ ΔL → Tm ΔL _) (CExt _)
           (lCtxₛ-factorExt-trimSub-assoc e s w)
           (rCtxₛ-factorExt-trimSub-assoc e s w)
           {t2 = substTm (subst (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s w) (factorSubₛ e (trimSub w s))) t}
           {e2 = subst₂ (CExt _) (lCtxₛ-factorExt-trimSub-assoc e s w) (rCtxₛ-factorExt-trimSub-assoc e s w) (factorExtₛ e (trimSub w s))}
           unbox
           (≅-cong (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s w) (λ s' → substTm s' t) (≡-subst-addable _ _ _))
           (≡-subst₂-addable _ _ _ _) ⟩
    unbox
      (substTm (subst (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s w) (factorSubₛ e (trimSub w s))) t)
      (subst₂ (CExt _) (lCtxₛ-factorExt-trimSub-assoc e s w) (rCtxₛ-factorExt-trimSub-assoc e s w) (factorExtₛ e (trimSub w s)))
      -- apply factoring equalities
      ≡⟨ cong₂ unbox (cong₂ substTm {u = t} (factorSubₛ-trimSub-comm e s w) ≡-refl) (factorExtₛ-trimSub-comm e s w) ⟩
    unbox
      (substTm (trimSub (factorWk e w) (factorSubₛ (factorExt e w) s)) t)
      (factorExtₛ (factorExt e w) s)
      -- aplpy IH
      ≡⟨ cong₂ unbox (coh-trimSub-wkTm t _ _) ≡-refl ⟩
    unbox
      (substTm (factorSubₛ (factorExt e w) s) (wkTm (factorWk e w) t))
      (factorExtₛ (factorExt e w) s)
      ≡⟨⟩
    (substTm s (wkTm w (unbox t e))) ∎

coh-trimSub-wkSub  : {Δ₁ : Ctx} (s : Sub Δ Γ) (s' : Sub Δ₁ Δ') (w : Δ ⊆ Δ')
         → s ∙ₛ (trimSub w s') ≡ (wkSub w s) ∙ₛ s'
coh-trimSub-wkSub []         s' w
  = ≡-refl
coh-trimSub-wkSub (s `, x)   s' w
  = cong₂ _`,_ (coh-trimSub-wkSub s s' w) (coh-trimSub-wkTm x s' w)
coh-trimSub-wkSub (lock s e) s' w
  = let open ≡-Reasoning in begin
    lock s e ∙ₛ trimSub w s'
      ≡⟨⟩
    lock
      (s ∙ₛ factorSubₛ e (trimSub w s'))
      (factorExtₛ e (trimSub w s'))
      -- add substs
      ≅⟨ xcong
           (λ ΓL → Sub ΓL _) (CExt _)
           (lCtxₛ-factorExt-trimSub-assoc e s' w) (rCtxₛ-factorExt-trimSub-assoc e s' w)
           lock
           (≅-cong  (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s' w) (s ∙ₛ_) (≡-subst-addable _ _ _))
           (≡-subst₂-addable (CExt _) _ _ (factorExtₛ e (trimSub w s'))) ⟩
    lock
      (s ∙ₛ (subst (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s' w) (factorSubₛ e (trimSub w s'))))
      (subst₂ (CExt _) (lCtxₛ-factorExt-trimSub-assoc e s' w) (rCtxₛ-factorExt-trimSub-assoc e s' w) (factorExtₛ e (trimSub w s')))
      -- apply factoring equalities
      ≡⟨ cong₂ lock (cong (s ∙ₛ_) (factorSubₛ-trimSub-comm e s' w)) (factorExtₛ-trimSub-comm e s' w) ⟩
    lock
       (s ∙ₛ (trimSub (factorWk e w) (factorSubₛ (factorExt e w) s')))
       (factorExtₛ (factorExt e w) s')
      -- apply IH
      ≡⟨ cong₂ lock (coh-trimSub-wkSub _ _ _) ≡-refl ⟩
    lock
      (wkSub (factorWk e w) s ∙ₛ factorSubₛ (factorExt e w) s')
      (factorExtₛ (factorExt e w) s')
      ≡⟨⟩
    (wkSub w (lock s e) ∙ₛ s') ∎

lCtxₛPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → lCtxₛ e (factorSubₛ e' s) ≡ lCtxₛ (extRAssoc e e') s
lCtxₛPresTrans e nil        s          = ≡-refl
lCtxₛPresTrans e (ext e')   (s `, _)   = lCtxₛPresTrans e e' s
lCtxₛPresTrans e (ext#- e') (lock s _) = lCtxₛPresTrans e e' s

rCtxₛPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → rCtxₛ e (factorSubₛ e' s) ,, rCtxₛ e' s ≡ rCtxₛ (extRAssoc e e') s
rCtxₛPresTrans e nil        s                    = ≡-refl
rCtxₛPresTrans e (ext e')   (s `, t)             = rCtxₛPresTrans e e' s
rCtxₛPresTrans e (ext#- e') (lock {ΔR = ΔR} s _) = ≡-trans (≡-sym (,,-assoc {ΓR = ΔR})) (cong (_,, ΔR) (rCtxₛPresTrans e e' s))

lCtxₛPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → lCtxₛ e (s ∙ₛ s') ≡ lCtxₛ (factorExtₛ e s) s'
lCtxₛPres∙ₛ nil       s s'           = ≡-refl
lCtxₛPres∙ₛ (ext e)   (s `, t) s'    = lCtxₛPres∙ₛ e s s'
lCtxₛPres∙ₛ (ext#- e) (lock s e1) s' = ≡-trans (lCtxₛPres∙ₛ e _ _) (lCtxₛPresTrans _ e1 _)

rCtxₛPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → rCtxₛ e (s ∙ₛ s') ≡ rCtxₛ (factorExtₛ e s) s'
rCtxₛPres∙ₛ nil       s s'           = ≡-refl
rCtxₛPres∙ₛ (ext e)   (s `, t) s'    = rCtxₛPres∙ₛ e s s'
rCtxₛPres∙ₛ (ext#- e) (lock s e1) s' = ≡-trans (cong (_,, _) (rCtxₛPres∙ₛ e _ _)) (rCtxₛPresTrans _ e1 _)

factorSubPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → subst (λ ΔL → Sub ΔL ΓLL) (lCtxₛPresTrans e e' s) (factorSubₛ e (factorSubₛ e' s)) ≡ factorSubₛ (extRAssoc e e') s
factorSubPresTrans e nil        s          = ≡-refl
factorSubPresTrans e (ext e')   (s `, _)   = factorSubPresTrans e e' s
factorSubPresTrans e (ext#- e') (lock s _) = factorSubPresTrans e e' s

factorSubPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → subst (λ ΔL → Sub ΔL ΓL) (lCtxₛPres∙ₛ e s s') (factorSubₛ e (s ∙ₛ s'))  ≡ factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) s'
factorSubPres∙ₛ nil       s           s' = ≡-refl
factorSubPres∙ₛ (ext e)   (s `, t)    s' = factorSubPres∙ₛ e s s'
factorSubPres∙ₛ (ext#- e) (lock s e1) s' = let open ≡-Reasoning in begin
  subst (λ ΔL → Sub ΔL _)
    (lCtxₛPres∙ₛ (ext#- e) (lock s e1) s')
    (factorSubₛ (ext#- e) (lock s e1 ∙ₛ s'))
    ≡⟨⟩
  subst (λ ΔL → Sub ΔL _)
    (≡-trans (lCtxₛPres∙ₛ e s (factorSubₛ e1 s')) (lCtxₛPresTrans (factorExtₛ e s) e1 s'))
    (factorSubₛ e (s ∙ₛ factorSubₛ e1 s'))
    -- split `subst _ (≡-trans p q) ...` to `subst _ q (subst _ p ...)`
    ≡⟨ ≡-sym (subst-subst (lCtxₛPres∙ₛ e s (factorSubₛ e1 s'))) ⟩
  subst (λ ΔL → Sub ΔL _)
    (lCtxₛPresTrans (factorExtₛ e s) e1 s')
    (subst (λ ΔL → Sub ΔL _)
      (lCtxₛPres∙ₛ e s (factorSubₛ e1 s'))
      (factorSubₛ e (s ∙ₛ factorSubₛ e1 s')))
    -- rewrite (remove) inner subst with IH
    ≡⟨ cong (subst (λ ΔL → Sub ΔL _) _) (factorSubPres∙ₛ e s (factorSubₛ e1 s')) ⟩
  subst (λ ΔL → Sub ΔL _)
    (lCtxₛPresTrans (factorExtₛ e s) e1 s')
    (factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) (factorSubₛ e1 s'))
    -- push subst inside application of (_ ∙ₛ_)
    ≡⟨ subst-application′  (λ ΔL → Sub ΔL _) (factorSubₛ e s ∙ₛ_) (lCtxₛPresTrans (factorExtₛ e s) e1 s') ⟩
  factorSubₛ e s ∙ₛ subst (λ ΔL → Sub ΔL _) (lCtxₛPresTrans (factorExtₛ e s) e1 s') (factorSubₛ (factorExtₛ e s) (factorSubₛ e1 s'))
    -- apply factorSubPresTrans
    ≡⟨ cong (_ ∙ₛ_) (factorSubPresTrans (factorExtₛ e s) e1 s') ⟩
  factorSubₛ e s ∙ₛ factorSubₛ (extRAssoc (factorExtₛ e s) e1) s'
    ≡⟨⟩
  factorSubₛ (ext#- e) (lock s e1) ∙ₛ factorSubₛ (factorExtₛ (ext#- e) (lock s e1)) s'   ∎

factorExtPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → subst₂ (CExt _) (lCtxₛPres∙ₛ e s s') (rCtxₛPres∙ₛ e s s') (factorExtₛ e (s ∙ₛ s')) ≡ factorExtₛ (factorExtₛ e s) s'
factorExtPres∙ₛ _ _ _ = ExtIsProp _ _

substVarPresId : (x : Var Γ a) → substVar idₛ x ≡ var x
substVarPresId zero     = ≡-refl
substVarPresId (succ x) = ≡-trans (nat-substVar x idₛ fresh) (≡-trans
  (cong (wkTm fresh) (substVarPresId x))
  (cong var (wkIncr x)))

-- parallel substitution (substVar) preserves substitution composition
substVarPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substTm s' (substVar s x) ≡ substVar (s ∙ₛ s') x
substVarPres∙ (s `, x) s' zero      = ≡-refl
substVarPres∙ (s `, x) s' (succ x₁) = substVarPres∙ s s' x₁

private
  dropKeepLemma : (s' : Sub Δ' Δ) (s : Sub Γ Δ')
    →  dropₛ (s' ∙ₛ s) ≡ dropₛ {a = a} s' ∙ₛ keepₛ s
  dropKeepLemma s' s = ≡-trans (coh-wkSub-∙ₛ s' s fresh)
    (≡-trans
      ((cong (s' ∙ₛ_) (≡-sym (trimSubPresId (dropₛ s)))))
      (coh-trimSub-wkSub s' (keepₛ s) fresh))

substTmPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm s' (substTm s t) ≡ substTm (s ∙ₛ s') t
substTmPres∙ s s' (var v) = substVarPres∙ s s' v
substTmPres∙ s s' (lam t) = cong lam
    (≡-trans (substTmPres∙ _ _ t)
    (cong ((λ s → substTm (s `, var zero) t)) (≡-sym (dropKeepLemma s s'))))
substTmPres∙ s s' (app t t₁) = cong₂ app (substTmPres∙ s s' t) (substTmPres∙ s s' t₁)
substTmPres∙ s s' (box t) = cong box (substTmPres∙ _ _ t)
substTmPres∙ {Δ = Δ} {a = a} s s' (unbox t e) = let open ≡-Reasoning in begin
  substTm s' (substTm s (unbox t e))
    ≡⟨⟩
  unbox
    (substTm (factorSubₛ (factorExtₛ e s) s') (substTm (factorSubₛ e s) t))
    (factorExtₛ (factorExtₛ e s) s')
    -- apply IH
    ≡⟨ cong₂ unbox (substTmPres∙ _ _ t) ≡-refl ⟩
  unbox
    (substTm (factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) s') t)
    (factorExtₛ (factorExtₛ e s) s')
    -- apply factoring equalities
    ≡⟨ cong₂ unbox (cong (λ x → substTm x t) (≡-sym (factorSubPres∙ₛ e _ _))) (≡-sym (factorExtPres∙ₛ e _ _)) ⟩
  unbox
    (substTm (subst (λ ΔL → Sub ΔL _) (lCtxₛPres∙ₛ e s s') (factorSubₛ e (s ∙ₛ s'))) t)
    (subst₂ (CExt _) (lCtxₛPres∙ₛ e s s') (rCtxₛPres∙ₛ e s s') (factorExtₛ e (s ∙ₛ s')))
    -- remove substs
    ≅⟨ xcong
      (λ ΓL → Tm ΓL (□ a)) (CExt Δ)
      (≡-sym (lCtxₛPres∙ₛ e s s')) (≡-sym (rCtxₛPres∙ₛ e s s'))
      {t2 = substTm (factorSubₛ e (s ∙ₛ s')) t}
      {e2 = factorExtₛ e (s ∙ₛ s')}
      unbox
      (≅-cong (λ ΔL → Sub ΔL _) (≡-sym (lCtxₛPres∙ₛ e s s')) (λ x → substTm x t) (≡-subst-removable _ _ _))
      (≡-subst₂-removable _ _ _ _) ⟩
  unbox (substTm (factorSubₛ e (s ∙ₛ s')) t) (factorExtₛ e (s ∙ₛ s'))
    ≡⟨⟩
  substTm (s ∙ₛ s') (unbox t e) ∎

assocSub : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (s3 : Sub Γ3 Γ4) (s2 : Sub Γ2 Γ3) → (s1 : Sub Γ1 Γ2)
  → (s3 ∙ₛ s2) ∙ₛ s1 ≡ s3 ∙ₛ (s2 ∙ₛ s1)
assocSub []           s2 s1 = ≡-refl
assocSub (s3 `, t)    s2 s1 = cong₂ _`,_ (assocSub s3 s2 s1) (substTmPres∙ s2 s1 t)
assocSub {Γ1 = Γ1} (lock s3 e3) s2 s1 = let open ≡-Reasoning in begin
  (lock s3 e3 ∙ₛ s2) ∙ₛ s1
    ≡⟨⟩
  lock
    ((s3 ∙ₛ factorSubₛ e3 s2) ∙ₛ factorSubₛ (factorExtₛ e3 s2) s1)
    (factorExtₛ (factorExtₛ e3 s2) s1)
    -- apply IH
    ≡⟨ cong₂ lock (assocSub _ _ _) ≡-refl ⟩
  lock
    (s3 ∙ₛ (factorSubₛ e3 s2 ∙ₛ factorSubₛ (factorExtₛ e3 s2) s1))
    (factorExtₛ (factorExtₛ e3 s2) s1)
    -- apply factoring equalities
    ≡⟨ cong₂ lock (cong (s3 ∙ₛ_) (≡-sym (factorSubPres∙ₛ e3 _ _ ))) (≡-sym (factorExtPres∙ₛ e3 _ _)) ⟩
  lock
    (s3 ∙ₛ subst (λ ΔL → Sub ΔL _) (lCtxₛPres∙ₛ e3 s2 s1) (factorSubₛ e3 (s2 ∙ₛ s1)))
    (subst₂ (CExt _) (lCtxₛPres∙ₛ e3 s2 s1) (rCtxₛPres∙ₛ e3 s2 s1) (factorExtₛ e3 (s2 ∙ₛ s1)))
    -- remove substs
    ≅⟨ xcong (λ ΔL → Sub ΔL _)
      (CExt Γ1)
      (≡-sym (lCtxₛPres∙ₛ e3 s2 s1)) (≡-sym (rCtxₛPres∙ₛ e3 s2 s1))
      {t2 = s3 ∙ₛ factorSubₛ e3 (s2 ∙ₛ s1)}
      {e2 = factorExtₛ e3 (s2 ∙ₛ s1)}
      lock
      (≅-cong (λ ΔL → Sub ΔL _) (≡-sym (lCtxₛPres∙ₛ e3 s2 s1)) (s3 ∙ₛ_) (≡-subst-removable _ _ _))
      (≡-subst₂-removable _ _ _ _) ⟩
  lock (s3 ∙ₛ factorSubₛ e3 (s2 ∙ₛ s1)) (factorExtₛ e3 (s2 ∙ₛ s1))
    ≡⟨⟩
  lock s3 e3 ∙ₛ (s2 ∙ₛ s1) ∎

leftIdSub : (s : Sub Γ Γ') → (idₛ ∙ₛ s) ≡ s
leftIdSub []         = ≡-refl
leftIdSub (s `, t)   = let open ≡-Reasoning in begin
  idₛ ∙ₛ (s `, t)
    ≡⟨⟩
  (wkSub fresh idₛ ∙ₛ (s `, t)) `, t
    ≡⟨ cong (_`, _) (≡-sym (coh-trimSub-wkSub idₛ (s `, t) fresh)) ⟩
  idₛ ∙ₛ trimSub fresh (s `, t) `, t
    ≡⟨ cong (_`, _) (≡-trans (leftIdSub _) (trimSubPresId _)) ⟩
  (s `, t) ∎
leftIdSub {Γ = Γ} (lock {ΔL = ΔL} {ΔR = ΔR} s e) = let open ≡-Reasoning in begin
  lock (idₛ ∙ₛ s) (extRAssoc nil e)
    ≡⟨ cong₂ lock (leftIdSub s) extLeftUnit ⟩
  lock s (subst (CExt Γ ΔL) _ e)
    ≅⟨ ≅-cong (CExt Γ ΔL) ,,-leftUnit (lock s) (≡-subst-removable (CExt Γ ΔL) _ e) ⟩
  lock s e ∎

private
  -- just a helper to reduce redundancy, nothing too interesting
  auxLemma : (w : Γ ⊆ Δ) → wkSub (drop[ a ] (w ∙ idWk)) idₛ ≡ dropₛ (embWk w)

wkSubId : (w : Γ ⊆ Δ) → wkSub w idₛ ≡ embWk w

auxLemma w = (≡-trans
    (≡-sym (wkSubPres∙ w fresh idₛ))
    (cong (wkSub fresh) (wkSubId w)))

wkSubId base      = ≡-refl
wkSubId (drop w)  = ≡-trans
  (cong (λ w' → wkSub (drop w') idₛ) (≡-sym (rightIdWk w)))
  (auxLemma w)
wkSubId (keep w)  = cong (_`, var zero) (≡-trans
  (wkSubPres∙ fresh (keep w) idₛ)
  (≡-trans
    (cong₂ wkSub (cong drop (≡-trans (leftIdWk _) (≡-sym (rightIdWk _)))) ≡-refl)
    (auxLemma w)))
wkSubId (keep# w) = cong₂ lock (wkSubId w) ≡-refl

-- Outcast lemmas

keepFreshLemma : {w : Γ ⊆ Γ'} {t : Tm Γ a}
  → wkTm fresh[ b ] (wkTm w t) ≡ wkTm (keep w) (wkTm fresh t)
keepFreshLemma = ≡-trans (wkTmPres∙ _ _ _) (≡-sym (≡-trans
    (wkTmPres∙ _ _ _)
    (cong₂ wkTm (cong drop (≡-trans (leftIdWk _) (≡-sym (rightIdWk _)))) ≡-refl)))

sliceCompLemma : (w : Γ ⊆ Δ) (e : LFExt Γ (ΓL #) ΓR) (t : Tm (ΓL #) a)
  → wkTm (LFExtToWk (wkLFExt e w)) (wkTm (keep# (sliceLeft e w)) t) ≡      wkTm w (wkTm (LFExtToWk e) t)
sliceCompLemma w e t = (≡-trans (wkTmPres∙ _ _ _) (≡-sym (≡-trans
  (wkTmPres∙ _ _ _)
  (cong₂ wkTm (slicingLemma w e) ≡-refl))))

beta-wk-lemma : (w  : Γ ⊆ Δ) (u : Tm Γ a) (t : Tm (Γ `, a) b)
  → substTm (idₛ `, wkTm w u) (wkTm (keep w) t) ≡ wkTm w (substTm (idₛ `, u) t)
beta-wk-lemma w u t = ≡-trans
  (≡-sym (coh-trimSub-wkTm t _ (keep w)))
  (≡-sym (≡-trans
    (≡-sym (nat-substTm t _ _))
    (cong
      (λ p → substTm (p `, wkTm w u) t)
      (≡-sym (≡-trans (trimSubId w) (≡-sym (wkSubId w)))))))

-- factorising the identity substituion yields a weakening that only drops
factorSubₛIdWkIsFactorSubₛId : (e : CExt Γ ΓL ΓR) → factorSubₛ e idₛ ≡ embWk (LFExtToWk (factorSubₛIdWk e))
factorSubₛIdWkIsFactorSubₛId nil             = ≡-refl
factorSubₛIdWkIsFactorSubₛId (ext#- e)       = factorSubₛIdWkIsFactorSubₛId e
factorSubₛIdWkIsFactorSubₛId (ext {a = a} e) = let open ≡-Reasoning in begin
  factorSubₛ e (wkSub fresh idₛ)
    -- apply `factorSubₛ-wkSub-comm`
    ≡⟨ subst-sym (lCtxₛ-wkSub-comm e fresh idₛ) (factorSubₛ-wkSub-comm e idₛ fresh)  ⟩
  subst (λ ΔL → Sub ΔL _) (≡-sym (lCtxₛ-wkSub-comm e fresh idₛ))
    (wkSub (factorWk (factorExtₛ e idₛ) fresh) (factorSubₛ e idₛ))
    -- apply IH
    ≡⟨ cong
        (λ z → subst (λ ΔL → Sub ΔL _) (≡-sym (lCtxₛ-wkSub-comm e fresh idₛ)) (wkSub (factorWk (factorExtₛ e idₛ) fresh) z))
        (factorSubₛIdWkIsFactorSubₛId e) ⟩
  subst (λ ΔL → Sub ΔL _) (≡-sym (lCtxₛ-wkSub-comm e fresh idₛ))
    (wkSub (factorWk (factorExtₛ e idₛ) fresh) (embWk (LFExtToWk (factorSubₛIdWk e))))
    -- apply `substCrunch` which crunches substitution with substitution and weakening equalities
    ≡⟨ cong
        (λ z → subst (λ ΔL → Sub ΔL _)
        (≡-sym (lCtxₛ-wkSub-comm e fresh idₛ)) z) substCrunch ⟩
  subst (λ ΔL → Sub ΔL _) (≡-sym (lCtxₛ-wkSub-comm e fresh idₛ))
    (embWk (LFExtToWk (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))))
    -- pull out subst
    ≡⟨ subst-application′ (λ Γ → LFExt Γ _ _)
         (λ z → embWk (LFExtToWk z))
         (≡-sym (lCtxₛ-wkSub-comm e fresh idₛ)) ⟩
  embWk (LFExtToWk
    (subst (λ Γ → LFExt Γ _ (←#₁rCtx e ,, rCtx′ (factorExtₛ e idₛ) freshExt)) (≡-sym (lCtxₛ-wkSub-comm e fresh idₛ))
      (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))))
    ≡⟨⟩
  embWk (LFExtToWk (factorSubₛIdWk (ext e))) ∎
  where
  --
  coh-wkSub-embwk : (w : Γ' ⊆ Γ'') (w' : Γ ⊆ Γ') → wkSub w (embWk w') ≡ embWk (w' ∙ w)
  coh-wkSub-embwk w w' = let open ≡-Reasoning in begin
    wkSub w (embWk w')
      ≡⟨ cong (wkSub w) (≡-sym (wkSubId _)) ⟩
    wkSub w (wkSub w' idₛ)
      ≡⟨ wkSubPres∙ _ _ _ ⟩
    wkSub (w' ∙ w) idₛ
      ≡⟨ wkSubId _ ⟩
    embWk (w' ∙ w) ∎
  --
  substCrunch : wkSub (factorWk (factorExtₛ e idₛ) fresh[ a ]) (embWk (LFExtToWk (factorSubₛIdWk e)))
    ≡ embWk (LFExtToWk (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt)))
  substCrunch = let open ≡-Reasoning in begin
    wkSub (factorWk (factorExtₛ e idₛ) fresh[ a ]) (embWk (LFExtToWk (factorSubₛIdWk e)))
      ≡⟨ coh-wkSub-embwk (factorWk (factorExtₛ e idₛ) fresh[ a ]) (LFExtToWk (factorSubₛIdWk e)) ⟩
    embWk (LFExtToWk (factorSubₛIdWk e) ∙ factorWk (factorExtₛ e idₛ) fresh)
      ≡⟨ cong (λ x → embWk (LFExtToWk (factorSubₛIdWk e) ∙ x)) (≡-sym (factorDropsWkIsfactorWk (factorExtₛ e idₛ) freshExt)) ⟩
    embWk (LFExtToWk (factorSubₛIdWk e) ∙ LFExtToWk (factorDropsWk (factorExtₛ e idₛ) freshExt))
      ≡⟨ cong embWk (≡-sym (LFExtToWkPresTrans (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))) ⟩
    embWk
      (LFExtToWk (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))) ∎

-----------------------------------
--- Reduction and conversion lemmas
-----------------------------------

wkTmPres⟶ : (w : Γ ⊆ Γ') → t ⟶ t' → wkTm w t ⟶ wkTm w t'
wkTmPres⟶ w (red-fun t u)
  = step-≡ (red-fun _ _) (beta-wk-lemma w u t)
wkTmPres⟶ w (exp-fun _)
  = step-≡ (exp-fun _) (cong lam (cong₂ app keepFreshLemma ≡-refl))
wkTmPres⟶ w (red-box t e)
  = step-≡
    (red-box _ _)
    (≡-trans
      (≡-˘trans
        (coh-trimSub-wkTm t _ _)
        (cong
          (λ s → substTm (lock s (factorExt e w)) t)
          (≡-trans
            (trimSubId (factorWk e w))
            (≡-sym (wkSubId _)))))
      (nat-substTm t _ _))
wkTmPres⟶ w (exp-box _)
  = exp-box _
wkTmPres⟶ w (cong-lam r)
  = cong-lam (wkTmPres⟶ (keep w) r)
wkTmPres⟶ w (cong-box r)
  = cong-box (wkTmPres⟶ (keep# w) r)
wkTmPres⟶ w (cong-unbox {e = e} r)
  = cong-unbox (wkTmPres⟶ (factorWk e w ) r)
wkTmPres⟶ w (cong-app1 r)
  = cong-app1 (wkTmPres⟶ w r)
wkTmPres⟶ w (cong-app2 r)
  = cong-app2 (wkTmPres⟶ w r)
wkTmPres⟶ w (shift-unbox t e e')
  = ≡-step-≡
    (let open ≡-Reasoning in begin
    wkTm w (unbox t (extRAssoc (upLFExt e) e'))
      ≡⟨⟩
    unbox
      (wkTm (factorWk (extRAssoc (upLFExt e) e') w) t)
      (factorExt (extRAssoc (upLFExt e) e') w)
      -- add substs
      ≡⟨ ≅-to-≡ (cong-unbox≅
        (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w)
        (≡-subst-addable _ _ _) (≡-subst₂-addable _ _ _ _)) ⟩
    unbox
      (subst (λ ΓL → Tm ΓL _) (lCtxPresTrans (upLFExt e) e' w) (wkTm (factorWk (extRAssoc (upLFExt e) e') w) t))
      (subst₂ (CExt _) (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w) (factorExt (extRAssoc (upLFExt e) e') w))
      -- push subst on subterm inside
      ≡⟨ cong₂ unbox (subst-application′ (_ ⊆_) (λ w → wkTm w t) (lCtxPresTrans (upLFExt e) e' w)) ≡-refl ⟩
   unbox
      (wkTm (subst (_ ⊆_) (lCtxPresTrans (upLFExt e) e' w) (factorWk (extRAssoc (upLFExt e) e') w)) t)
      (subst₂ (CExt _) (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w) (factorExt (extRAssoc (upLFExt e) e') w))
      -- factorisation preserves transitivity
      ≡⟨ cong₂ unbox (cong₂ wkTm (factorWkPresTrans (upLFExt e) e' w) ≡-refl) (factorExtPresTrans (upLFExt e) _ _) ⟩
    unbox
      (wkTm (factorWk (upLFExt e) (factorWk e' w)) t)
      (extRAssoc (factorExt (upLFExt e) (factorWk e' w)) (factorExt e' w))
      -- apply equalities for absorption of upLFExt
      ≡⟨ cong₂ unbox (cong₂ wkTm (≡-sym (factorWkAbsorbsUpLFExt e (factorWk e' w))) ≡-refl) (cong₂ extRAssoc (≡-sym (factorExtAbsorbsUpLFExt e (factorWk e' w))) ≡-refl) ⟩
    unbox
      (wkTm (subst (_ ⊆_) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (factorWk e (factorWk e' w))) t)
      (extRAssoc (subst₂ (CExt _) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (rCtxAbsorbsUpLFExt e (factorWk e' w)) (upLFExt (factorExt e (factorWk e' w)))) (factorExt e' w))
      -- pull out substs
      ≡⟨ cong₂ unbox (≡-sym (subst-application′ (_ ⊆_) (λ x → wkTm x t) (lCtxAbsorbsUpLFExt e (factorWk e' w)))) (ExtIsProp _ _) ⟩
    unbox
      (subst (λ ΓL → Tm ΓL _) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (wkTm (factorWk e (factorWk e' w)) t))
      (subst₂ (λ ΓL ΓR → CExt _ ΓL (ΓR ,, _)) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (rCtxAbsorbsUpLFExt e (factorWk e' w)) (extRAssoc (upLFExt (factorExt e (factorWk e' w))) (factorExt e' w)))
      -- remove substs
      ≡⟨ ≅-to-≡ (cong-unbox≅
        (≡-sym (lCtxAbsorbsUpLFExt e (factorWk e' w))) (cong (_,, _) (≡-sym (rCtxAbsorbsUpLFExt e (factorWk e' w))))
        (≡-subst-removable _ _ _) (≡-subst₂-removable _ _ _ _)) ⟩
    unbox
      (wkTm (factorWk e (factorWk e' w)) t)
      (extRAssoc (upLFExt (factorExt e (factorWk e' w))) (factorExt e' w)) ∎)
    (shift-unbox _ _ _)
    (let open ≡-Reasoning in begin
    unbox
      (wkTm (LFExtToWk (factorExt e (factorWk e' w))) (wkTm (factorWk e (factorWk e' w)) t))
      (factorExt e' w)
      -- wkTm preserves composition
      ≡⟨ cong₂ unbox (wkTmPres∙ _ _ _) ≡-refl ⟩
    unbox
      (wkTm (factorWk e (factorWk e' w) ∙ LFExtToWk (factorExt e (factorWk e' w))) t)
      (factorExt e' w)
      -- apply factorisationLemma
      ≡⟨ cong₂ unbox (cong₂ wkTm (≡-sym (factorisationLemma e _)) ≡-refl) ≡-refl ⟩
    unbox
      (wkTm (LFExtToWk e ∙ factorWk e' w) t)
      (factorExt e' w)
      -- wkTm preserves composition
      ≡⟨ cong₂ unbox (≡-sym (wkTmPres∙ _ _ _)) ≡-refl ⟩
    unbox
      (wkTm (factorWk e' w) (wkTm (LFExtToWk e) t))
      (factorExt e' w)
      ≡⟨⟩
    wkTm w (unbox (wkTm (LFExtToWk e) t) e') ∎)

wkTmPres≈ : (w : Γ ⊆ Γ') → t ≈ t' → wkTm w t ≈ wkTm w t'
wkTmPres≈ w = cong-⟶-to-cong-≈ (wkTmPres⟶ w)

wkSubPres⟶ : (w : Δ ⊆ Δ') → σ ⟶ₛ σ' → wkSub w σ ⟶ₛ wkSub w σ'
wkSubPres⟶ w (cong-`,⟶ₛ1 r) = cong-`,⟶ₛ1 (wkSubPres⟶ w r)
wkSubPres⟶ w (cong-`,⟶ₛ2 r) = cong-`,⟶ₛ2 (wkTmPres≈ w r)
wkSubPres⟶ w (cong-lock⟶ₛ r) = cong-lock⟶ₛ (wkSubPres⟶ _ r)
wkSubPres⟶ w (shift-lock⟶ₛ {s = s} w' {e}) = RUtil.≡-step-≡ _⟶ₛ_
  (let open ≡-Reasoning in begin
  wkSub w (lock s (extRAssoc (upLFExt w') e))
     ≡⟨⟩
  lock
    (wkSub (factorWk (extRAssoc (upLFExt w') e) w) s)
    (factorExt (extRAssoc (upLFExt w') e) w)
    -- add substs
    ≡⟨ ≅-to-≡ (cong-lock≅ (lCtxPresTrans (upLFExt w') e w) (rCtxPresTrans (upLFExt w') e w) (≡-subst-addable _ _ _) (≡-subst₂-addable _ _ _ _)) ⟩
  lock
    (subst (λ ΓL → Sub ΓL _) (lCtxPresTrans (upLFExt w') e w) (wkSub (factorWk (extRAssoc (upLFExt w') e) w) s))
    (subst₂ (CExt _) (lCtxPresTrans (upLFExt w') e w) (rCtxPresTrans (upLFExt w') e w) (factorExt (extRAssoc (upLFExt w') e) w))
    -- push subst on subterm inside
    ≡⟨ cong₂ lock (subst-application′ (_ ⊆_) (λ w → wkSub w s) (lCtxPresTrans (upLFExt w') e w)) ≡-refl ⟩
  lock
    (wkSub (subst (_ ⊆_) (lCtxPresTrans (upLFExt w') e w) (factorWk (extRAssoc (upLFExt w') e) w)) s)
    (subst₂ (CExt _) (lCtxPresTrans (upLFExt w') e w) (rCtxPresTrans (upLFExt w') e w) (factorExt (extRAssoc (upLFExt w') e) w))
    -- factorisation preserves transitivity
    ≡⟨ cong₂ lock (cong₂ wkSub (factorWkPresTrans (upLFExt w') e w) ≡-refl) (factorExtPresTrans (upLFExt w') _ _) ⟩
  lock
    (wkSub (factorWk (upLFExt w') (factorWk e w)) s)
    (extRAssoc (factorExt (upLFExt w') (factorWk e w)) (factorExt e w))
    -- apply equalities for absorption of upLFExt
    ≡⟨ cong₂ lock (cong₂ wkSub (≡-sym (factorWkAbsorbsUpLFExt w' (factorWk e w))) ≡-refl) (cong₂ extRAssoc (≡-sym (factorExtAbsorbsUpLFExt w' (factorWk e w))) ≡-refl) ⟩
  lock
    (wkSub (subst (_ ⊆_) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (factorWk w' (factorWk e w))) s)
    (extRAssoc (subst₂ (CExt _) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (rCtxAbsorbsUpLFExt w' (factorWk e w)) (upLFExt (factorExt w' (factorWk e w)))) (factorExt e w))
    -- pull out substs
    ≡⟨ cong₂ lock (≡-sym (subst-application′ (_ ⊆_) (λ x → wkSub x s) (lCtxAbsorbsUpLFExt w' (factorWk e w)))) (ExtIsProp _ _) ⟩
  lock
    (subst (λ ΓL → Sub ΓL _) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (wkSub (factorWk w' (factorWk e w)) s))
    (subst₂ (λ ΓL ΓR → CExt _ ΓL (ΓR ,, _)) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (rCtxAbsorbsUpLFExt w' (factorWk e w)) (extRAssoc (upLFExt (factorExt w' (factorWk e w))) (factorExt e w)))
    -- remove substs
    ≡⟨ ≅-to-≡ (cong-lock≅ (≡-sym (lCtxAbsorbsUpLFExt w' (factorWk e w))) (≡-sym (cong (_,, _) (rCtxAbsorbsUpLFExt w' (factorWk e w)))) (≡-subst-removable _ _ _) (≡-subst₂-removable _ _ _ _)) ⟩
  lock
   (wkSub (factorWk w' (factorWk e w)) s)
   (extRAssoc (upLFExt (factorExt w' (factorWk e w))) (factorExt e w)) ∎)
  (shift-lock⟶ₛ _)
  (let open ≡-Reasoning in begin
  lock
   (wkSub (LFExtToWk (factorExt w' (factorWk e w))) (wkSub (factorWk w' (factorWk e w)) s))
   (factorExt e w)
   -- wkSub preserves composition
   ≡⟨ cong₂ lock (wkSubPres∙ _ _ _) ≡-refl ⟩
  lock
   (wkSub (factorWk w' (factorWk e w) ∙ LFExtToWk (factorExt w' (factorWk e w))) s)
   (factorExt e w)
   -- apply factorisation lemma
   ≡⟨ cong₂ lock (cong₂ wkSub (≡-sym (factorisationLemma w' _)) ≡-refl) ≡-refl ⟩
  lock
   (wkSub (LFExtToWk w' ∙ factorWk e w) s)
   (factorExt e w)
   -- wkSub preserves composition
   ≡⟨ cong₂ lock (≡-sym (wkSubPres∙ _ _ _)) ≡-refl ⟩
  lock
   (wkSub (factorWk e w) (wkSub (LFExtToWk w') s))
   (factorExt e w)
   ≡⟨⟩
  wkSub w (lock (wkSub (LFExtToWk w') s) e) ∎)

wkSubPres≈ : (w : Δ ⊆ Δ') → σ ≈ₛ σ' → wkSub w σ ≈ₛ wkSub w σ'
wkSubPres≈ w = cong-⟶ₛ-to-cong-≈ₛ (wkSubPres⟶ w)

fact-ext≅ : (e : CExt Γ ΓL ΓR)
  → e ≅ extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ)
fact-ext≅ e = ≅-trans
  (≡-subst-addable _ _ _)
  (≡-to-≅ (ExtIsProp′ e (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))))

substTmPresId : (t : Tm Γ a) → t ≈ substTm idₛ t
substTmPresId (var x)     = ≈-reflexive˘ (substVarPresId x)
substTmPresId (lam t)     = cong-lam≈ (substTmPresId t)
substTmPresId (app t u)   = cong-app≈ (substTmPresId t) (substTmPresId u)
substTmPresId (box t)     = cong-box≈ (substTmPresId t)
substTmPresId (unbox t e) = fact-unbox≈ t e
  where
  --
  coh-wkTm-substTm : (t : Tm Γ a) (w : Γ ⊆ Γ') → wkTm w t ≈ substTm (embWk w) t
  coh-wkTm-substTm {a = a} {Γ' = Γ'} t w = begin
    wkTm w t
      -- apply IH
      ≈⟨ wkTmPres≈ w (substTmPresId t) ⟩
    wkTm w (substTm idₛ t)
      -- apply naturality of substTm
      ≡⟨ ≡-sym (nat-substTm t idₛ w) ⟩
    substTm (wkSub w idₛ) t
      -- weakening id subst is same as embedding the weakening into a subst
      ≡⟨ cong₂ substTm {u = t} (wkSubId w) ≡-refl ⟩
    substTm (embWk w) t ∎
    where
    open SetoidReasoning (Tm-setoid Γ' a)
  --
  fact-unbox≈ : (t : Tm ΓL (□ a)) (e : CExt Γ ΓL ΓR)
    → unbox t e ≈ unbox (substTm (factorSubₛ e idₛ) t) (factorExtₛ e idₛ)
  fact-unbox≈ {a = a} {Γ = Γ} t e = begin
    unbox t e
      -- expand extension e
      ≡⟨ ≅-to-≡ (cong-unbox≅ ≡-refl (extRUniq e (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))) ≅-refl (fact-ext≅ e)) ⟩
    unbox t (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))
      -- apply shift-unbox
      ≈⟨ ⟶-to-≈ (shift-unbox _ _ _) ⟩
    unbox (wkTm (LFExtToWk (factorSubₛIdWk e)) t) (factorExtₛ e idₛ)
      -- rewrite wkTm to substTm
      ≈⟨ cong-unbox1≈ (coh-wkTm-substTm t _) ⟩
    unbox (substTm (embWk (LFExtToWk (factorSubₛIdWk e))) t) (factorExtₛ e idₛ)
      -- show that the subst is the factorisation of the id subst
      ≡⟨ cong₂ unbox (cong₂ substTm {u = t} (≡-sym (factorSubₛIdWkIsFactorSubₛId e)) ≡-refl) ≡-refl ⟩
    unbox (substTm (factorSubₛ e idₛ) t) (factorExtₛ e idₛ) ∎
    where
    open SetoidReasoning (Tm-setoid Γ a)

rightIdSub : (s : Sub Γ Γ') → s ≈ₛ (s ∙ₛ idₛ)
rightIdSub []         = ≈ₛ-refl
rightIdSub (s `, t)   = cong-`,≈ₛ (rightIdSub s) (substTmPresId t)
rightIdSub (lock s e) = fact-lock≈ s e
  where
  --
  fact-lock≈ : (s : Sub ΓL Δ) (e : CExt Γ ΓL ΓR)
    → lock s e ≈ₛ lock (s ∙ₛ factorSubₛ e idₛ) (factorExtₛ e idₛ)
  fact-lock≈ {Δ = Δ} {Γ = Γ} s e = begin
    lock s e
      -- expand extension e
      ≡⟨ ≅-to-≡ (cong-lock≅ ≡-refl (extRUniq e (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))) ≅-refl (fact-ext≅ e)) ⟩
    lock s (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))
      -- apply shift-lock≈ₛ
      ≈⟨ shift-lock≈ₛ _ ⟩
    lock (wkSub (LFExtToWk (factorSubₛIdWk e)) s) (factorExtₛ e idₛ)
      -- apply IH
      ≈⟨ cong-lock≈ₛ (wkSubPres≈ _ (rightIdSub s)) ⟩
    lock (wkSub (LFExtToWk (factorSubₛIdWk e)) (s ∙ₛ idₛ)) (factorExtₛ e idₛ)
      -- rewrite using coherence between weakening and composing substs (associativity, really)
      ≡⟨ cong₂ lock (coh-wkSub-∙ₛ s idₛ (LFExtToWk (factorSubₛIdWk e))) ≡-refl ⟩
    lock (s ∙ₛ wkSub (LFExtToWk (factorSubₛIdWk e)) idₛ) (factorExtₛ e idₛ)
      --  weakening of id subst is itself a weakening
      ≡⟨ cong₂ lock (cong (s ∙ₛ_) (wkSubId _)) ≡-refl ⟩
    lock (s ∙ₛ (embWk (LFExtToWk (factorSubₛIdWk e)))) (factorExtₛ e idₛ)
      -- show that the weakening subst is the factorisation of the id subst
      ≡⟨ cong₂ lock (cong (s ∙ₛ_) (≡-sym (factorSubₛIdWkIsFactorSubₛId e))) ≡-refl ⟩
    lock (s ∙ₛ factorSubₛ e idₛ) (factorExtₛ e idₛ) ∎
    where
    open SetoidReasoning (Sub-setoid Γ (Δ #))

substVarPres⟶ : (v : Var Γ a) → σ ⟶ₛ σ' → substVar σ v ≈ substVar σ' v
substVarPres⟶ zero     (cong-`,⟶ₛ1 s⟶s') = ≈-refl
substVarPres⟶ zero     (cong-`,⟶ₛ2 t≈t') = t≈t'
substVarPres⟶ (succ v) (cong-`,⟶ₛ1 s⟶s') = substVarPres⟶ v s⟶s'
substVarPres⟶ (succ v) (cong-`,⟶ₛ2 t≈t') = ≈-refl

-- XXX: fold
substVarPres≈ : (v : Var Γ a) → σ ≈ₛ σ' → substVar σ v ≈ substVar σ' v
substVarPres≈ v ε                    = ≈-refl
substVarPres≈ v (inj₁ σ⟶σ' ◅ σ'≈σ'') = ≈-trans (substVarPres⟶ v σ⟶σ') (substVarPres≈ v σ'≈σ'')
substVarPres≈ v (inj₂ σ'⟶σ ◅ σ≈σ'')  = ≈-˘trans (substVarPres⟶ v σ'⟶σ) (substVarPres≈ v σ≈σ'')

substTmPres⟶ : (t : Tm Γ a) → σ ⟶ₛ σ' → substTm σ t ≈ substTm σ' t
substTmPres⟶ (var v)     r = substVarPres⟶ v r
substTmPres⟶ (lam t)     r = cong-lam≈ (substTmPres⟶ t (cong-`,⟶ₛ1 (wkSubPres⟶ fresh r)))
substTmPres⟶ (app t u)   r = cong-app≈ (substTmPres⟶ t r) (substTmPres⟶ u r)
substTmPres⟶ (box t)     r = cong-box≈ (substTmPres⟶ t (cong-lock⟶ₛ r))
substTmPres⟶ (unbox t e) r = h e r t
  where
    h : ∀ (e    : CExt Γ ΓL ΓR)
          (σ⟶σ' : σ ⟶ₛ σ')
          (t    : Tm ΓL (□ a))
          {e'   : CExt Θ _ ΔR}
          {e''  : CExt Θ _ ΔR'}
        → unbox (substTm (factorSubₛ e σ)  t) e'
        ≈ unbox (substTm (factorSubₛ e σ') t) e''
    h nil        σ⟶ₛσ'                   t = cong-unbox≈ (substTmPres⟶ t σ⟶ₛσ')
    h (ext e)    (cong-`,⟶ₛ1 σ⟶σ')       t = h e σ⟶σ' t
    h (ext e)    (cong-`,⟶ₛ2 t≈t')       t = cong-unbox2≈
    h (ext#- e) (cong-lock⟶ₛ σ⟶σ')       t = h e σ⟶σ' t
    h (ext#- e) (shift-lock⟶ₛ {s = σ} w) t {e'} {e''} = let open SetoidReasoning (Tm-setoid _ _) in
        begin
          unbox (substTm (factorSubₛ e σ) t) e'
        ≈⟨ shift-unbox≈ (substTm (factorSubₛ e σ) t) (factorDropsWk (factorExtₛ e σ) w) ⟩
          unbox (wkTm (LFExtToWk (factorDropsWk (factorExtₛ e σ) w)) (substTm (factorSubₛ e σ) t)) (subst (λ Δ → CExt _ Δ _) (lCtxₛ-wkSub-comm e (LFExtToWk w) σ) e'')
        ≡⟨ cong (λ w' → unbox (wkTm w' _) (subst (λ Δ → CExt _ Δ _) (lCtxₛ-wkSub-comm e (LFExtToWk w) σ) e'')) (factorDropsWkIsfactorWk (factorExtₛ e σ) w) ⟩
          unbox (wkTm (factorWk (factorExtₛ e σ) (LFExtToWk w)) (substTm (factorSubₛ e σ) t)) (subst (λ Δ → CExt _ Δ _) (lCtxₛ-wkSub-comm e (LFExtToWk w) σ) e'')
        ≡˘⟨ cong₂ unbox (nat-substTm t (factorSubₛ e σ) (factorWk (factorExtₛ e σ) (LFExtToWk w))) ≡-refl ⟩
          unbox (substTm (wkSub (factorWk (factorExtₛ e σ) (LFExtToWk w)) (factorSubₛ e σ)) t) (subst (λ Δ → CExt _ Δ _) (lCtxₛ-wkSub-comm e (LFExtToWk w) σ) e'')
        ≡˘⟨ dcong₃ (λ _Δ s e → unbox (substTm s t) e) (lCtxₛ-wkSub-comm e (LFExtToWk w) σ) (factorSubₛ-wkSub-comm e σ (LFExtToWk w)) ≡-refl ⟩
          unbox (substTm (factorSubₛ e (wkSub (LFExtToWk w) σ)) t) e''
        ∎

-- XXX: fold
substTmPres≈ : (t : Tm Γ a) → (σ≈σ' : σ ≈ₛ σ') → substTm σ t ≈ substTm σ' t
substTmPres≈ t ε                    = ≈-refl
substTmPres≈ t (inj₁ σ⟶σ' ◅ σ'≈σ'') = ≈-trans (substTmPres⟶ t σ⟶σ') (substTmPres≈ t σ'≈σ'')
substTmPres≈ t (inj₂ σ'⟶σ ◅ σ≈σ'')  = ≈-˘trans (substTmPres⟶ t σ'⟶σ) (substTmPres≈ t σ≈σ'')
