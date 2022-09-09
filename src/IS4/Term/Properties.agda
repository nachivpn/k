{-# OPTIONS --safe --without-K #-}
module IS4.Term.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst-subst ; module ≡-Reasoning)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import PEUtil
import RUtil

open import IS4.Term.Base
open import IS4.Term.Conversion
open import IS4.Term.Reduction

open import Context.Properties          Ty Ty-Decidable as ContextProperties
open import Weakening.Properties        Ty              as WeakeningProperties
open import ContextExtension.Properties Ty Ty-Decidable as ContextExtensionProperties
open import Variable.Properties         Ty              as VariableProperties

open ContextProperties          public
open WeakeningProperties        public
open ContextExtensionProperties public
open VariableProperties         public

----------------------
-- Substitution lemmas
----------------------

-- Left context of weakening and applying a substituion
-- is the same as the
-- Left context of applying and then weakening it
lCtxₛ-wkSub-comm : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → lCtxₛ e (wkSub w s) ≡ lCtx (factorExtₛ e s) w
lCtxₛ-wkSub-comm nil       _s          _w = refl
lCtxₛ-wkSub-comm (ext   e) (s `, _t)   w  = lCtxₛ-wkSub-comm e s w
lCtxₛ-wkSub-comm (ext#- e) (lock s e') w  = trans˘
  (lCtxₛ-wkSub-comm e s (factorWk e' w))
  (lCtxPresTrans (factorExtₛ e _) e' _)

-- Right context of weakening and applying a substituion
-- is the same as the
-- Right context of applying and then weakening it
rCtxₛ-wkSub-comm : (e : CExt Γ ΓL ΓR) (s  : Sub Δ Γ) (w : Δ ⊆ Δ')
  → rCtxₛ e (wkSub w s) ≡ rCtx (factorExtₛ e s) w
rCtxₛ-wkSub-comm nil       _s          _w = refl
rCtxₛ-wkSub-comm (ext   e) (s `, _t)   w  = rCtxₛ-wkSub-comm e s w
rCtxₛ-wkSub-comm (ext#- e) (lock s e') w  = trans˘
  (cong1 _,,_ (rCtxₛ-wkSub-comm e s (factorWk e' w)))
  (rCtxPresTrans (factorExtₛ e _) e' _)

-- Weakening and factoring a subtitution can be achieved by factoring and then weakening it
factorSubₛ-wkSub-comm : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → subst1 Sub (lCtxₛ-wkSub-comm e s w) (factorSubₛ e (wkSub w s)) ≡ wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)
factorSubₛ-wkSub-comm nil       _s          _w = refl
factorSubₛ-wkSub-comm (ext   e) (s `, _t)   w  = factorSubₛ-wkSub-comm e s w
factorSubₛ-wkSub-comm (ext#- e) (lock s e') w  = let open ≡-Reasoning in begin
  subst1 Sub
    (trans˘ (lCtxₛ-wkSub-comm e _ _) (lCtxPresTrans _ e' _))
    (factorSubₛ e (wkSub (factorWk e' w) s))
    -- split `subst _ (trans p q) ...` to `subst _ q (subst _ p ...)`
    ≡˘⟨ subst-subst (lCtxₛ-wkSub-comm e _ _) ⟩
  subst1˘ Sub
    (lCtxPresTrans _ e' _)
    (subst1 Sub (lCtxₛ-wkSub-comm e _ _)
      (factorSubₛ e (wkSub (factorWk e' w) s)))
    -- rewrite inner subst
    ≡⟨ cong (subst1 Sub _) (factorSubₛ-wkSub-comm e s (factorWk e' w)) ⟩
  subst1˘ Sub
    (lCtxPresTrans _ e' _)
    (wkSub (factorWk (factorExtₛ e s) (factorWk e' w)) (factorSubₛ e s))
    -- commute subst with application
    ≡⟨ subst˘-application1′ wkSub (lCtxPresTrans _ e' _) ⟩
  wkSub
    (subst˘ (_ ⊆_)
      (lCtxPresTrans _ e' _)
      (factorWk (factorExtₛ e s) (factorWk e' w)))
    (factorSubₛ e s)
    -- apply factorWkPresTrans
    ≡˘⟨ cong1 wkSub (subst-sym (lCtxPresTrans _ e' _) (factorWkPresTrans (factorExtₛ e s) e' w)) ⟩
  wkSub (factorWk (extRAssoc (factorExtₛ e s) e') w) (factorSubₛ e s) ∎

lCtxₛ-factorExt-trimSub-assoc : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
   → lCtxₛ e (trimSub w s) ≡ lCtxₛ (factorExt e w) s
lCtxₛ-factorExt-trimSub-assoc nil       s          w
  = refl
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
  = refl
rCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, t)   (drop w)
  = rCtxₛ-factorExt-trimSub-assoc (ext e) s w
rCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, t)   (keep w)
  = rCtxₛ-factorExt-trimSub-assoc e s w
rCtxₛ-factorExt-trimSub-assoc (ext#- e) (s `, t)   (drop w)
  = rCtxₛ-factorExt-trimSub-assoc (ext#- e) s w
rCtxₛ-factorExt-trimSub-assoc (ext#- e) (lock s _) (keep# w)
  = cong (_,, _) (rCtxₛ-factorExt-trimSub-assoc e s w)

factorSubₛ-trimSub-comm : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → subst1 Sub (lCtxₛ-factorExt-trimSub-assoc e s w) (factorSubₛ e (trimSub w s)) ≡ trimSub (factorWk e w) (factorSubₛ (factorExt e w) s)
factorSubₛ-trimSub-comm nil       s          w
  = refl
factorSubₛ-trimSub-comm (ext e)   (s `, _)   (drop w)
  = factorSubₛ-trimSub-comm (ext e) s w
factorSubₛ-trimSub-comm (ext e)   (s `, _)   (keep w)
  = factorSubₛ-trimSub-comm e s w
factorSubₛ-trimSub-comm (ext#- e) (s `, t)   (drop w)
  = factorSubₛ-trimSub-comm (ext#- e) s w
factorSubₛ-trimSub-comm (ext#- e) (lock s _) (keep# w)
  = factorSubₛ-trimSub-comm e s w

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
  _ = refl

-- Given `e` that ΓL extends Γ, ΓL is a lock-free extension of `lCtxₛ e idₛ`.
-- This means that ΓL ⊆ (lCtxₛ e idₛ), and thus applying `factorSubₛ e idₛ` weakens
-- a term with variables in `←#₁rCtx e`
factorSubₛIdWk : (e : CExt Γ ΓL ΓR) → LFExt (lCtxₛ e idₛ) ΓL (←#₁rCtx e)
factorSubₛIdWk                nil              = nil
factorSubₛIdWk {ΓR = ΓR `, a} (ext {a = .a} e) = subst˘
  (λ Γ → LFExt Γ _ (←#₁rCtx (ext e))) (lCtxₛ-wkSub-comm e idₛ fresh)
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
  = refl
coh-trimSub-wkVar (succ x) (s `, x₁) (drop w)
  = coh-trimSub-wkVar (succ x) s w
coh-trimSub-wkVar (succ x) (s `, x₁) (keep w)
  = coh-trimSub-wkVar x s w

-- `trimSub` preserves the identity
trimSubPresId : (s : Sub Δ Γ) → trimSub idWk s ≡ s
trimSubPresId []         = refl
trimSubPresId (s `, t)   = cong1 _`,_ (trimSubPresId s)
trimSubPresId (lock s e) = cong1 lock (trimSubPresId s)

-- naturality of substVar
nat-substVar : (v : Var Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substVar (wkSub w s) v ≡ wkTm w (substVar s v)
nat-substVar zero     (s `, t) w = refl
nat-substVar (succ v) (s `, t) w = nat-substVar v s w

-- naturality of trimSub
nat-trimSub : (s : Sub Γ Δ) (w : Δ' ⊆ Δ) (w' : Γ ⊆ Γ')
  → wkSub w' (trimSub w s) ≡ trimSub w (wkSub w' s)
nat-trimSub []         base      w' = refl
nat-trimSub (s `, t)   (drop  w) w' = nat-trimSub s w w'
nat-trimSub (s `, t)   (keep  w) w' = cong1 _`,_ (nat-trimSub s w w')
nat-trimSub (lock s e) (keep# w) w' = cong1 lock (nat-trimSub s w (factorWk e w'))

-- `trimSub` on the identity substitution embeds the weakening
trimSubId : (w : Γ ⊆ Δ) → trimSub w idₛ ≡ embWk w
trimSubId base      = refl
trimSubId (drop w)  = ˘trans
  (nat-trimSub idₛ w fresh)
  (cong (wkSub fresh) (trimSubId w))
trimSubId (keep w)  = cong (_`, var zero) (˘trans
  (nat-trimSub idₛ w fresh)
  (cong (wkSub fresh) (trimSubId w)))
trimSubId (keep# w) = cong1 lock (trimSubId w)

---------------------------
-- Hell Of Syntactic Lemmas
---------------------------

-- Welcome to the hell of mind-numbing syntactic lemmas.
-- No good ever comes from proving these lemmas, but no
-- good can happen without proving them.

module _ {e : CExt Δ Γ ΓR} {e' : CExt Δ Γ' ΓR'} where
  cong-unbox≡′′ : (Γ≡Γ' : Γ ≡ Γ')
    → (t≡t' : subst1 Tm Γ≡Γ' t ≡ t')
    → unbox t e ≡ unbox t' e'
  cong-unbox≡′′ Γ≡Γ' t≡t' =
    idcong₄ unbox Γ≡Γ' (extRUniq′ Γ≡Γ' e e') t≡t' (ExtIsProp _ _)

cong-unbox≡ : (t≡t' : t ≡ t') → unbox t e ≡ unbox t' e
cong-unbox≡ = cong-unbox≡′′ refl

cong-unbox2≡ : unbox t e ≡ unbox t e'
cong-unbox2≡ = cong-unbox≡′′ refl refl

cong-unbox≡′ : (t≡t' : t ≡ t') → unbox t e ≡ unbox t' e'
cong-unbox≡′ = cong-unbox≡′′ refl

module _ {e : CExt Δ Γ ΓR} {e' : CExt Δ Γ' ΓR'} where
  cong-lock≡′′ : (Γ≡Γ' : Γ ≡ Γ')
    → (s≡s' : subst1 Sub Γ≡Γ' s ≡ s')
    → lock s e ≡ lock s' e'
  cong-lock≡′′ Γ≡Γ' s≡s' =
    idcong₄ lock Γ≡Γ' (extRUniq′ Γ≡Γ' e e') s≡s' (ExtIsProp _ _)

cong-lock≡ : (s≡s' : s ≡ s') → lock s e ≡ lock s' e
cong-lock≡ = cong-lock≡′′ refl

cong-lock2≡ : lock s e ≡ lock s e'
cong-lock2≡ = cong-lock≡′′ refl refl

cong-lock≡′ : (s≡s' : s ≡ s') → lock s e ≡ lock s' e'
cong-lock≡′ = cong-lock≡′′ refl

wkTmPresId : (t : Tm Γ a) → wkTm idWk t ≡ t
wkTmPresId (var   v)   = cong  var (wkVarPresId v)
wkTmPresId (lam   t)   = cong  lam (wkTmPresId  t)
wkTmPresId (app   t u) = cong₂ app (wkTmPresId  t) (wkTmPresId u)
wkTmPresId (box   t)   = cong  box (wkTmPresId  t)
wkTmPresId (unbox t e) = let open ≡-Reasoning in begin
  wkTm idWk (unbox t e)
    ≡⟨⟩
  unbox (wkTm (factorWk e idWk) t) (factorExt e idWk)
    ≡⟨ cong-unbox≡′′
         (lCtxPresId e)
         (trans
           (subst-application1′ wkTm (lCtxPresId e))
           (cong1 wkTm (factorWkPresId e)))
     ⟩
  unbox (wkTm idWk t) e
    ≡⟨ cong1 unbox (wkTmPresId t) ⟩
  unbox t e ∎

wkSubPresId : (s : Sub Δ Γ) → wkSub idWk s ≡ s
wkSubPresId []         = refl
wkSubPresId (s `, t)   = cong₂ _`,_ (wkSubPresId s) (wkTmPresId t)
wkSubPresId (lock s e) = let open ≡-Reasoning in begin
  wkSub idWk (lock s e)
    ≡⟨⟩
  lock (wkSub (factorWk e idWk) s) (factorExt e idWk)
    ≡⟨ cong-lock≡′′
         (lCtxPresId e)
         (trans
           (subst-application1′ wkSub (lCtxPresId e))
           (cong1 wkSub (factorWkPresId e)))
     ⟩
  lock (wkSub idWk s) e
    ≡⟨ cong1 lock (wkSubPresId s) ⟩
  lock s e ∎

wkTmPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (t : Tm Γ a)
  → wkTm w' (wkTm w t) ≡ wkTm (w ∙ w') t
wkTmPres∙ w w' (var   v)   = cong  var (wkVarPres∙ w w' v)
wkTmPres∙ w w' (lam   t)   = cong  lam (wkTmPres∙ (keep w) (keep w') t)
wkTmPres∙ w w' (app   t u) = cong₂ app (wkTmPres∙ w w' t) (wkTmPres∙ w w' u)
wkTmPres∙ w w' (box   t)   = cong  box (wkTmPres∙ (keep# w) (keep# w') t)
wkTmPres∙ w w' (unbox t e) = let open ≡-Reasoning in begin
  wkTm w' (wkTm w (unbox t e))
    ≡⟨⟩
  unbox
    (wkTm (factorWk (factorExt e w) w') (wkTm (factorWk e w) t))
    (factorExt (factorExt e w) w')
    ≡⟨ cong-unbox≡′ (wkTmPres∙ _ _ t) ⟩
  unbox
    (wkTm (factorWk e w ∙ factorWk (factorExt e w) w') t)
    (factorExt (factorExt e w) w')
    ≡˘⟨ cong-unbox≡′′
          (lCtxPres∙ e w w')
          (trans
            (subst-application1′ wkTm (lCtxPres∙ e w w'))
            (cong1 wkTm (factorWkPres∙ e w w')))
      ⟩
  unbox
    (wkTm (factorWk e (w ∙ w')) t)
    (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkTm (w ∙ w') (unbox t e) ∎

wkSubPres∙ : (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') (s : Sub Δ Γ)
  → wkSub w' (wkSub w s) ≡ wkSub (w ∙ w') s
wkSubPres∙ _w _w' []         = refl
wkSubPres∙ w  w'  (s `, t)   = cong₂ _`,_ (wkSubPres∙ w w' s) (wkTmPres∙ w w' t)
wkSubPres∙ w  w'  (lock s e) = let open ≡-Reasoning in begin
  wkSub w' (wkSub w (lock s e))
    ≡⟨⟩
  lock
    (wkSub (factorWk (factorExt e w) w') (wkSub (factorWk e w) s))
    (factorExt (factorExt e w) w')
    ≡⟨ cong1 lock (wkSubPres∙ _ _ _ ) ⟩
  lock
    (wkSub (factorWk e w ∙ factorWk (factorExt e w) w') s)
    (factorExt (factorExt e w) w')
    ≡˘⟨ cong-lock≡′′
          (lCtxPres∙ e w w')
          (trans
            (subst-application1′ wkSub (lCtxPres∙ e w w'))
            (cong1 wkSub (factorWkPres∙ e w w')))
     ⟩
  lock
    (wkSub (factorWk e (w ∙ w')) s)
    (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkSub (w ∙ w') (lock s e) ∎

private
  wkSubFreshLemma : {s : Sub Δ Γ} {w : Δ ⊆ Δ'}
    → wkSub fresh[ a ] (wkSub w s) ≡ wkSub (keep w) (dropₛ s)
  wkSubFreshLemma {s = s} {w} = trans
    (wkSubPres∙ w fresh s)
    (trans˘
      (cong1 wkSub (cong drop (rightIdWk _)) )
      (trans
        (wkSubPres∙ _ _ _)
        (cong1 wkSub (cong drop (leftIdWk _)))))

nat-substTm : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
nat-substTm (var   v)   s w
  = nat-substVar v s w
nat-substTm (lam   t)   s w
  = cong lam
    (trans (cong (λ s → substTm (s `, var zero) t) wkSubFreshLemma)
    (nat-substTm t (keepₛ s) (keep w)))
nat-substTm (app   t u) s w
  = cong₂ app (nat-substTm t s w) (nat-substTm u s w)
nat-substTm (box   t)   s w
  = cong box (nat-substTm t (lock s (ext#- nil)) (keep# w))
nat-substTm (unbox t e) s w
  = let open ≡-Reasoning in begin
      substTm (wkSub w s) (unbox t e)
        ≡⟨⟩
      unbox
        (substTm (factorSubₛ e (wkSub w s)) t)
        (factorExtₛ e (wkSub w s))
        ≡⟨ cong-unbox≡′′
             (lCtxₛ-wkSub-comm e s w)
             (trans
               (subst-application1′ substTm {z = t} (lCtxₛ-wkSub-comm e s w))
               (cong1 substTm {y = t} (factorSubₛ-wkSub-comm e s w)))
         ⟩
     unbox
        (substTm (wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)) t)
        (factorExt (factorExtₛ e s) w)
        ≡⟨ cong-unbox≡ (nat-substTm t _ _) ⟩
      unbox
        (wkTm (factorWk (factorExtₛ e s) w) (substTm (factorSubₛ e s) t))
        (factorExt (factorExtₛ e s) w)
        ≡⟨⟩
      wkTm w (substTm s (unbox t e)) ∎

coh-wkSub-∙ₛ  : {Δ'' : Ctx} (s : Sub Δ Γ) (s' : Sub Δ' Δ) (w : Δ' ⊆ Δ'')
         → wkSub w (s ∙ₛ s') ≡ s ∙ₛ wkSub w s'
coh-wkSub-∙ₛ []         _s' _w = refl
coh-wkSub-∙ₛ (s `, t)   s'  w  = cong₂ _`,_ (coh-wkSub-∙ₛ s s' w) (sym (nat-substTm t s' w))
coh-wkSub-∙ₛ (lock s e) s'  w  = let open ≡-Reasoning in begin
  wkSub w (lock s e ∙ₛ s')
    ≡⟨⟩
  lock
    (wkSub (factorWk (factorExtₛ e s') w) (s ∙ₛ factorSubₛ e s'))
    (factorExt (factorExtₛ e s') w)
    -- apply IH
    ≡⟨ cong1 lock (coh-wkSub-∙ₛ _ _ _) ⟩
 lock
   (s ∙ₛ wkSub (factorWk (factorExtₛ e s') w) (factorSubₛ e s'))
   (factorExt (factorExtₛ e s') w)
   -- applying factoring equalities
   ≡˘⟨ cong-lock≡′′
         (lCtxₛ-wkSub-comm e s' w)
         (trans
           (subst-application′ (s ∙ₛ_) (lCtxₛ-wkSub-comm e s' w))
           (cong (s ∙ₛ_) (factorSubₛ-wkSub-comm e s' w))) ⟩
 lock
   (s ∙ₛ factorSubₛ e (wkSub w s'))
   (factorExtₛ e (wkSub w s'))
   ≡⟨⟩
 lock s e ∙ₛ wkSub w s' ∎

coh-trimSub-wkTm : (t : Tm Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substTm (trimSub w s) t ≡ substTm s (wkTm w t)
coh-trimSub-wkTm (var   v)   s w
  = coh-trimSub-wkVar v s w
coh-trimSub-wkTm (lam   t)   s w
  = cong lam (trans
    (cong (λ p → substTm (p `, var zero) t) (nat-trimSub s w fresh))
    (coh-trimSub-wkTm t (keepₛ s) (keep w)))
coh-trimSub-wkTm (app   t u) s w
  = cong₂ app (coh-trimSub-wkTm t s w) (coh-trimSub-wkTm u s w)
coh-trimSub-wkTm (box   t)   s w
  = cong box (coh-trimSub-wkTm t (lock s (ext#- nil)) (keep# w))
coh-trimSub-wkTm (unbox t e) s w
  = let open ≡-Reasoning in begin
      substTm (trimSub w s) (unbox t e)
        ≡⟨⟩
      unbox
        (substTm (factorSubₛ e (trimSub w s)) t)
        (factorExtₛ e (trimSub w s))
        -- apply factoring equalities
        ≡⟨ cong-unbox≡′′
             (lCtxₛ-factorExt-trimSub-assoc e s w)
             (trans
               (subst-application1′ substTm {z = t} (lCtxₛ-factorExt-trimSub-assoc e s w))
               (cong1 substTm {y = t} (factorSubₛ-trimSub-comm e s w)))
         ⟩
      unbox
        (substTm (trimSub (factorWk e w) (factorSubₛ (factorExt e w) s)) t)
        (factorExtₛ (factorExt e w) s)
        -- aplpy IH
        ≡⟨ cong1 unbox (coh-trimSub-wkTm t _ _) ⟩
      unbox
        (substTm (factorSubₛ (factorExt e w) s) (wkTm (factorWk e w) t))
        (factorExtₛ (factorExt e w) s)
        ≡⟨⟩
      substTm s (wkTm w (unbox t e)) ∎

coh-trimSub-wkSub : {Δ₁ : Ctx} (s : Sub Δ Γ) (s' : Sub Δ₁ Δ') (w : Δ ⊆ Δ')
         → s ∙ₛ trimSub w s' ≡ wkSub w s ∙ₛ s'
coh-trimSub-wkSub []         _s' _w
  = refl
coh-trimSub-wkSub (s `, t)   s'  w
  = cong₂ _`,_ (coh-trimSub-wkSub s s' w) (coh-trimSub-wkTm t s' w)
coh-trimSub-wkSub (lock s e) s'  w
  = let open ≡-Reasoning in begin
      lock s e ∙ₛ trimSub w s'
        ≡⟨⟩
      lock
        (s ∙ₛ factorSubₛ e (trimSub w s'))
        (factorExtₛ e (trimSub w s'))
        -- apply factoring equalities
        ≡⟨ cong-lock≡′′
             (lCtxₛ-factorExt-trimSub-assoc e s' w)
             (trans
               (subst-application′ (s ∙ₛ_) (lCtxₛ-factorExt-trimSub-assoc e s' w))
               (cong (s ∙ₛ_) (factorSubₛ-trimSub-comm e s' w)))
         ⟩
      lock
         (s ∙ₛ trimSub (factorWk e w) (factorSubₛ (factorExt e w) s'))
         (factorExtₛ (factorExt e w) s')
        -- apply IH
        ≡⟨ cong1 lock (coh-trimSub-wkSub _ _ _) ⟩
      lock
        (wkSub (factorWk e w) s ∙ₛ factorSubₛ (factorExt e w) s')
        (factorExtₛ (factorExt e w) s')
        ≡⟨⟩
      wkSub w (lock s e) ∙ₛ s' ∎

lCtxₛPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → lCtxₛ e (factorSubₛ e' s) ≡ lCtxₛ (extRAssoc e e') s
lCtxₛPresTrans _e nil        _s            = refl
lCtxₛPresTrans e  (ext   e') (s `, _t)     = lCtxₛPresTrans e e' s
lCtxₛPresTrans e  (ext#- e') (lock s _e'') = lCtxₛPresTrans e e' s

rCtxₛPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → rCtxₛ e (factorSubₛ e' s) ,, rCtxₛ e' s ≡ rCtxₛ (extRAssoc e e') s
rCtxₛPresTrans _e nil        _s                      = refl
rCtxₛPresTrans e  (ext   e') (s `, _t)               = rCtxₛPresTrans e e' s
rCtxₛPresTrans e  (ext#- e') (lock {ΔR = ΔR} s _e'') = ˘trans (,,-assoc {ΓR = ΔR}) (cong (_,, ΔR) (rCtxₛPresTrans e e' s))

lCtxₛPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → lCtxₛ e (s ∙ₛ s') ≡ lCtxₛ (factorExtₛ e s) s'
lCtxₛPres∙ₛ nil       _s          _s' = refl
lCtxₛPres∙ₛ (ext   e) (s `, _t)   s'  = lCtxₛPres∙ₛ e s s'
lCtxₛPres∙ₛ (ext#- e) (lock s e') s'  = trans (lCtxₛPres∙ₛ e _ _) (lCtxₛPresTrans _ e' _)

rCtxₛPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → rCtxₛ e (s ∙ₛ s') ≡ rCtxₛ (factorExtₛ e s) s'
rCtxₛPres∙ₛ nil       _s          _s' = refl
rCtxₛPres∙ₛ (ext   e) (s `, _t)   s'  = rCtxₛPres∙ₛ e s s'
rCtxₛPres∙ₛ (ext#- e) (lock s e') s'  = trans (cong (_,, _) (rCtxₛPres∙ₛ e _ _)) (rCtxₛPresTrans _ e' _)

factorSubPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → subst1 Sub (lCtxₛPresTrans e e' s) (factorSubₛ e (factorSubₛ e' s)) ≡ factorSubₛ (extRAssoc e e') s
factorSubPresTrans _e nil        _s            = refl
factorSubPresTrans e  (ext   e') (s `, _t)     = factorSubPresTrans e e' s
factorSubPresTrans e  (ext#- e') (lock s _e'') = factorSubPresTrans e e' s

factorSubPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → subst1 Sub (lCtxₛPres∙ₛ e s s') (factorSubₛ e (s ∙ₛ s'))  ≡ factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) s'
factorSubPres∙ₛ nil       _s          _s' = refl
factorSubPres∙ₛ (ext   e) (s `, _t)   s'  = factorSubPres∙ₛ e s s'
factorSubPres∙ₛ (ext#- e) (lock s e') s'  = let open ≡-Reasoning in begin
  subst1 Sub
    (lCtxₛPres∙ₛ (ext#- e) (lock s e') s')
    (factorSubₛ (ext#- e) (lock s e' ∙ₛ s'))
    ≡⟨⟩
  subst1 Sub
    (trans (lCtxₛPres∙ₛ e s (factorSubₛ e' s')) (lCtxₛPresTrans (factorExtₛ e s) e' s'))
    (factorSubₛ e (s ∙ₛ factorSubₛ e' s'))
    -- split `subst _ (trans p q) ...` to `subst _ q (subst _ p ...)`
    ≡˘⟨ subst-subst (lCtxₛPres∙ₛ e s (factorSubₛ e' s')) ⟩
  subst1 Sub
    (lCtxₛPresTrans (factorExtₛ e s) e' s')
    (subst1 Sub
      (lCtxₛPres∙ₛ e s (factorSubₛ e' s'))
      (factorSubₛ e (s ∙ₛ factorSubₛ e' s')))
    -- rewrite (remove) inner subst with IH
    ≡⟨ cong (subst1 Sub _) (factorSubPres∙ₛ e s (factorSubₛ e' s')) ⟩
  subst1 Sub
    (lCtxₛPresTrans (factorExtₛ e s) e' s')
    (factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) (factorSubₛ e' s'))
    -- push subst inside application of (_ ∙ₛ_)
    ≡⟨ subst-application′ (factorSubₛ e s ∙ₛ_) (lCtxₛPresTrans (factorExtₛ e s) e' s') ⟩
  factorSubₛ e s ∙ₛ subst1 Sub (lCtxₛPresTrans (factorExtₛ e s) e' s') (factorSubₛ (factorExtₛ e s) (factorSubₛ e' s'))
    -- apply factorSubPresTrans
    ≡⟨ cong (_ ∙ₛ_) (factorSubPresTrans (factorExtₛ e s) e' s') ⟩
  factorSubₛ e s ∙ₛ factorSubₛ (extRAssoc (factorExtₛ e s) e') s'
    ≡⟨⟩
  factorSubₛ (ext#- e) (lock s e') ∙ₛ factorSubₛ (factorExtₛ (ext#- e) (lock s e')) s'   ∎

substVarPresId : (x : Var Γ a) → substVar idₛ x ≡ var x
substVarPresId zero     = refl
substVarPresId (succ x) = trans (nat-substVar x idₛ fresh) (trans
  (cong (wkTm fresh) (substVarPresId x))
  (cong var (wkIncr x)))

-- parallel substitution (substVar) preserves substitution composition
substVarPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substTm s' (substVar s x) ≡ substVar (s ∙ₛ s') x
substVarPres∙ (s `, x) s' zero      = refl
substVarPres∙ (s `, x) s' (succ x₁) = substVarPres∙ s s' x₁

private
  dropKeepLemma : (s' : Sub Δ' Δ) (s : Sub Γ Δ')
    → dropₛ (s' ∙ₛ s) ≡ dropₛ {a = a} s' ∙ₛ keepₛ s
  dropKeepLemma s' s = trans (coh-wkSub-∙ₛ s' s fresh)
    (˘trans
      (cong (s' ∙ₛ_) (trimSubPresId (dropₛ s)))
      (coh-trimSub-wkSub s' (keepₛ s) fresh))

substTmPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm s' (substTm s t) ≡ substTm (s ∙ₛ s') t
substTmPres∙ s s' (var   v)  = substVarPres∙ s s' v
substTmPres∙ s s' (lam   t)  = cong lam
  (trans˘
    (substTmPres∙ (keepₛ s) (keepₛ s') t)
    (cong (λ s → substTm (s `, var zero) t) (dropKeepLemma s s')))
substTmPres∙ s s' (app   t u) = cong₂ app (substTmPres∙ s s' t) (substTmPres∙ s s' u)
substTmPres∙ s s' (box   t)   = cong  box (substTmPres∙ (keep#ₛ s) (keep#ₛ s') t)
substTmPres∙ s s' (unbox t e) = let open ≡-Reasoning in begin
  substTm s' (substTm s (unbox t e))
    ≡⟨⟩
  unbox
    (substTm (factorSubₛ (factorExtₛ e s) s') (substTm (factorSubₛ e s) t))
    (factorExtₛ (factorExtₛ e s) s')
    -- apply IH
    ≡⟨ cong1 unbox (substTmPres∙ _ _ t) ⟩
  unbox
    (substTm (factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) s') t)
    (factorExtₛ (factorExtₛ e s) s')
    -- apply factoring equalities
    ≡˘⟨ cong-unbox≡′′
          (lCtxₛPres∙ₛ e s s')
          (trans
            (subst-application1′ substTm {z = t} (lCtxₛPres∙ₛ e s s'))
            (cong1 substTm {y = t} (factorSubPres∙ₛ e s s')))
      ⟩
  unbox
    (substTm (factorSubₛ e (s ∙ₛ s')) t)
    (factorExtₛ e (s ∙ₛ s'))
    ≡⟨⟩
  substTm (s ∙ₛ s') (unbox t e) ∎

assocSub : ∀ (s : Sub Δ Γ) (s' : Sub Θ Δ) (s'' : Sub Ξ Θ)
  → (s ∙ₛ s') ∙ₛ s'' ≡ s ∙ₛ (s' ∙ₛ s'')
assocSub []         _s' _s'' = refl
assocSub (s `, t)   s'  s''  = cong₂ _`,_ (assocSub s s' s'') (substTmPres∙ s' s'' t)
assocSub (lock s e) s'  s''  = let open ≡-Reasoning in begin
  (lock s e ∙ₛ s') ∙ₛ s''
    ≡⟨⟩
  lock
    ((s ∙ₛ factorSubₛ e s') ∙ₛ factorSubₛ (factorExtₛ e s') s'')
    (factorExtₛ (factorExtₛ e s') s'')
    -- apply IH
    ≡⟨ cong1 lock (assocSub _ _ _) ⟩
  lock
    (s ∙ₛ factorSubₛ e s' ∙ₛ factorSubₛ (factorExtₛ e s') s'')
    (factorExtₛ (factorExtₛ e s') s'')
    -- apply factoring equalities
    ≡˘⟨ cong-lock≡′′
          (lCtxₛPres∙ₛ e s' s'')
          (trans
            (subst-application′ (s ∙ₛ_) (lCtxₛPres∙ₛ e s' s''))
            (cong (s ∙ₛ_) (factorSubPres∙ₛ e _ _ )))
      ⟩
  lock
    (s ∙ₛ factorSubₛ e (s' ∙ₛ s''))
    (factorExtₛ e (s' ∙ₛ s''))
    ≡⟨⟩
  lock s e ∙ₛ (s' ∙ₛ s'') ∎

leftIdSub : (s : Sub Γ Γ') → idₛ ∙ₛ s ≡ s
leftIdSub []         = refl
leftIdSub (s `, t)   = let open ≡-Reasoning in begin
  idₛ ∙ₛ (s `, t)
    ≡⟨⟩
  wkSub fresh idₛ ∙ₛ (s `, t) `, t
    ≡˘⟨ cong (_`, _) (coh-trimSub-wkSub idₛ (s `, t) fresh) ⟩
  idₛ ∙ₛ trimSub fresh (s `, t) `, t
    ≡⟨ cong (_`, _) (trans (leftIdSub _) (trimSubPresId _)) ⟩
  (s `, t) ∎
leftIdSub (lock s e) = let open ≡-Reasoning in begin
  lock (idₛ ∙ₛ s) (extRAssoc nil e)
    ≡⟨ cong-lock≡′ (leftIdSub s) ⟩
  lock s e ∎

wkSubId : (w : Γ ⊆ Δ) → wkSub w idₛ ≡ embWk w

private
  -- just a helper to reduce redundancy, nothing too interesting
  auxLemma : (w : Γ ⊆ Δ) → wkSub (drop[ a ] (w ∙ idWk)) idₛ ≡ dropₛ (embWk w)
  auxLemma w = ˘trans (wkSubPres∙ w fresh idₛ) (cong (wkSub fresh) (wkSubId w))

wkSubId base      = refl
wkSubId (drop  w) = ˘trans
  (cong (λ w' → wkSub (drop w') idₛ) (rightIdWk w))
  (auxLemma w)
wkSubId (keep  w) = cong (_`, var zero) (trans
  (wkSubPres∙ fresh (keep w) idₛ)
  (trans
    (cong1 wkSub (cong drop (trans˘ (leftIdWk _) (rightIdWk _))))
    (auxLemma w)))
wkSubId (keep# w) = cong1 lock (wkSubId w)

-- Outcast lemmas

keepFreshLemma : {w : Γ ⊆ Γ'} {t : Tm Γ a}
  → wkTm fresh[ b ] (wkTm w t) ≡ wkTm (keep w) (wkTm fresh t)
keepFreshLemma = trans˘
  (wkTmPres∙ _ _ _)
  (trans
    (wkTmPres∙ _ _ _)
    (cong1 wkTm (cong drop (trans˘ (leftIdWk _) (rightIdWk _)))))

sliceCompLemma : (w : Γ ⊆ Δ) (e : LFExt Γ (ΓL #) ΓR) (t : Tm (ΓL #) a)
  → wkTm (LFExtToWk (wkLFExt e w)) (wkTm (keep# (sliceLeft e w)) t) ≡      wkTm w (wkTm (LFExtToWk e) t)
sliceCompLemma w e t = trans˘
  (wkTmPres∙ _ _ _)
  (trans
    (wkTmPres∙ _ _ _)
    (cong1 wkTm (slicingLemma w e)))

beta-wk-lemma : (w  : Γ ⊆ Δ) (u : Tm Γ a) (t : Tm (Γ `, a) b)
  → substTm (idₛ `, wkTm w u) (wkTm (keep w) t) ≡ wkTm w (substTm (idₛ `, u) t)
beta-wk-lemma w u t = ˘trans
  (coh-trimSub-wkTm t _ (keep w))
  (trans
    (cong
      (λ p → substTm (p `, wkTm w u) t)
      (trans˘ (trimSubId w) (wkSubId w)))
    (nat-substTm t _ _))

-- factorising the identity substituion yields a weakening that only drops
factorSubₛIdWkIsFactorSubₛId : (e : CExt Γ ΓL ΓR) → factorSubₛ e idₛ ≡ embWk (LFExtToWk (factorSubₛIdWk e))
factorSubₛIdWkIsFactorSubₛId nil             = refl
factorSubₛIdWkIsFactorSubₛId (ext#- e)       = factorSubₛIdWkIsFactorSubₛId e
factorSubₛIdWkIsFactorSubₛId (ext {a = a} e) = let open ≡-Reasoning in begin
  factorSubₛ e (wkSub fresh idₛ)
    -- apply `factorSubₛ-wkSub-comm`
    ≡⟨ subst-sym (lCtxₛ-wkSub-comm e idₛ fresh) (factorSubₛ-wkSub-comm e idₛ fresh)  ⟩
  subst1˘ Sub (lCtxₛ-wkSub-comm e idₛ fresh)
    (wkSub (factorWk (factorExtₛ e idₛ) fresh) (factorSubₛ e idₛ))
    -- apply IH
    ≡⟨ cong
         (λ z → subst1˘ Sub (lCtxₛ-wkSub-comm e idₛ fresh) (wkSub (factorWk (factorExtₛ e idₛ) fresh) z))
         (factorSubₛIdWkIsFactorSubₛId e) ⟩
  subst1˘ Sub (lCtxₛ-wkSub-comm e idₛ fresh)
    (wkSub (factorWk (factorExtₛ e idₛ) fresh) (embWk (LFExtToWk (factorSubₛIdWk e))))
    -- apply `substCrunch` which crunches substitution with substitution and weakening equalities
    ≡⟨ cong
         (subst1˘ Sub (lCtxₛ-wkSub-comm e idₛ fresh))
         substCrunch ⟩
  subst1˘ Sub (lCtxₛ-wkSub-comm e idₛ fresh)
    (embWk (LFExtToWk (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))))
    -- pull out subst
    ≡⟨ subst˘-application′
         (λ z → embWk (LFExtToWk z))
         (lCtxₛ-wkSub-comm e idₛ fresh) ⟩
  embWk (LFExtToWk
    (subst˘ (λ Γ → LFExt Γ _ (←#₁rCtx e ,, rCtx′ (factorExtₛ e idₛ) freshExt)) (lCtxₛ-wkSub-comm e idₛ fresh)
      (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))))
    ≡⟨⟩
  embWk (LFExtToWk (factorSubₛIdWk (ext e))) ∎
  where
  --
  coh-wkSub-embwk : (w : Γ' ⊆ Γ'') (w' : Γ ⊆ Γ') → wkSub w (embWk w') ≡ embWk (w' ∙ w)
  coh-wkSub-embwk w w' = let open ≡-Reasoning in begin
    wkSub w (embWk w')
      ≡˘⟨ cong (wkSub w) (wkSubId _) ⟩
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
      ≡˘⟨ cong (λ x → embWk (LFExtToWk (factorSubₛIdWk e) ∙ x)) (factorDropsWkIsfactorWk (factorExtₛ e idₛ) freshExt) ⟩
    embWk (LFExtToWk (factorSubₛIdWk e) ∙ LFExtToWk (factorDropsWk (factorExtₛ e idₛ) freshExt))
      ≡˘⟨ cong embWk (LFExtToWkPresTrans (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt)) ⟩
    embWk
      (LFExtToWk (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))) ∎

-----------------------------------
--- Reduction and conversion lemmas
-----------------------------------

wkTmPres⟶ : (w : Γ ⊆ Γ') → t ⟶ t' → wkTm w t ⟶ wkTm w t'
wkTmPres⟶ w (red-fun t u)
  = step-≡ (red-fun _ _) (beta-wk-lemma w u t)
wkTmPres⟶ w (exp-fun _)
  = step-≡ (exp-fun _) (cong lam (cong1 app keepFreshLemma))
wkTmPres⟶ w (red-box t e)
  = step-≡
    (red-box _ _)
    (trans
      (˘trans
        (coh-trimSub-wkTm t _ _)
        (cong
          (λ s → substTm (lock s (factorExt e w)) t)
          (trans˘
            (trimSubId (factorWk e w))
            (wkSubId _))))
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
wkTmPres⟶ w (shift-unbox t w' e)
  = ≡-step-≡
      (let open ≡-Reasoning in begin
        wkTm w (unbox t (extRAssoc (upLFExt w') e))
          ≡⟨⟩
        unbox
          (wkTm (factorWk (extRAssoc (upLFExt w') e) w) t)
          (factorExt (extRAssoc (upLFExt w') e) w)
          -- factorisation preserves transitivity
          ≡⟨ cong-unbox≡′′
               (lCtxPresTrans (upLFExt w') e w)
               (trans
                 (subst-application1′ wkTm (lCtxPresTrans (upLFExt w') e w))
                 (cong1 wkTm (factorWkPresTrans (upLFExt w') e w)))
           ⟩
        unbox
          (wkTm (factorWk (upLFExt w') (factorWk e w)) t)
          (extRAssoc (factorExt (upLFExt w') (factorWk e w)) (factorExt e w))
          -- apply equalities for absorption of upLFExt
          ≡˘⟨ cong-unbox≡′′
                (lCtxAbsorbsUpLFExt w' (factorWk e w))
                (trans
                  (subst-application1′ wkTm (lCtxAbsorbsUpLFExt w' (factorWk e w)))
                  (cong1 wkTm (factorWkAbsorbsUpLFExt w' (factorWk e w))))
            ⟩
        unbox
          (wkTm (factorWk w' (factorWk e w)) t)
          (extRAssoc (upLFExt (factorExt w' (factorWk e w))) (factorExt e w)) ∎)
      (shift-unbox _ _ _)
      (let open ≡-Reasoning in begin
        unbox
          (wkTm (LFExtToWk (factorExt w' (factorWk e w))) (wkTm (factorWk w' (factorWk e w)) t))
          (factorExt e w)
          -- wkTm preserves composition
          ≡⟨ cong1 unbox (wkTmPres∙ _ _ _) ⟩
        unbox
          (wkTm (factorWk w' (factorWk e w) ∙ LFExtToWk (factorExt w' (factorWk e w))) t)
          (factorExt e w)
          -- apply factorisationLemma
          ≡˘⟨ cong1 unbox (cong1 wkTm (factorisationLemma w' _)) ⟩
        unbox
          (wkTm (LFExtToWk w' ∙ factorWk e w) t)
          (factorExt e w)
          -- wkTm preserves composition
          ≡˘⟨ cong1 unbox (wkTmPres∙ _ _ _) ⟩
        unbox
          (wkTm (factorWk e w) (wkTm (LFExtToWk w') t))
          (factorExt e w)
          ≡⟨⟩
        wkTm w (unbox (wkTm (LFExtToWk w') t) e) ∎)

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
      -- factorisation preserves transitivity
      ≡⟨ cong-lock≡′′
           (lCtxPresTrans (upLFExt w') e w)
           (trans
             (subst-application1′ wkSub (lCtxPresTrans (upLFExt w') e w))
             (cong1 wkSub (factorWkPresTrans (upLFExt w') e w)))
       ⟩
    lock
      (wkSub (factorWk (upLFExt w') (factorWk e w)) s)
      (extRAssoc (factorExt (upLFExt w') (factorWk e w)) (factorExt e w))
      -- apply equalities for absorption of upLFExt
      ≡˘⟨ cong-lock≡′′
            (lCtxAbsorbsUpLFExt w' (factorWk e w))
            (trans
              (subst-application1′ wkSub (lCtxAbsorbsUpLFExt w' (factorWk e w)))
              (cong1 wkSub (factorWkAbsorbsUpLFExt w' (factorWk e w))))
        ⟩
    lock
      (wkSub (factorWk w' (factorWk e w)) s)
      (extRAssoc (upLFExt (factorExt w' (factorWk e w))) (factorExt e w)) ∎)
  (shift-lock⟶ₛ _)
  (let open ≡-Reasoning in begin
    lock
      (wkSub (LFExtToWk (factorExt w' (factorWk e w))) (wkSub (factorWk w' (factorWk e w)) s))
      (factorExt e w)
      -- wkSub preserves composition
      ≡⟨ cong1 lock (wkSubPres∙ _ _ _) ⟩
    lock
      (wkSub (factorWk w' (factorWk e w) ∙ LFExtToWk (factorExt w' (factorWk e w))) s)
      (factorExt e w)
      -- apply factorisation lemma
      ≡˘⟨ cong1 lock (cong1 wkSub (factorisationLemma w' _)) ⟩
    lock
      (wkSub (LFExtToWk w' ∙ factorWk e w) s)
      (factorExt e w)
      -- wkSub preserves composition
      ≡˘⟨ cong1 lock (wkSubPres∙ _ _ _) ⟩
    lock
      (wkSub (factorWk e w) (wkSub (LFExtToWk w') s))
      (factorExt e w)
      ≡⟨⟩
    wkSub w (lock (wkSub (LFExtToWk w') s) e) ∎)

wkSubPres≈ : (w : Δ ⊆ Δ') → σ ≈ₛ σ' → wkSub w σ ≈ₛ wkSub w σ'
wkSubPres≈ w = cong-⟶ₛ-to-cong-≈ₛ (wkSubPres⟶ w)

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
      ≡˘⟨ nat-substTm t idₛ w ⟩
    substTm (wkSub w idₛ) t
      -- weakening id subst is same as embedding the weakening into a subst
      ≡⟨ cong1 substTm {y = t} (wkSubId w) ⟩
    substTm (embWk w) t ∎
    where
    open SetoidReasoning (Tm-setoid Γ' a)
  --
  fact-unbox≈ : (t : Tm ΓL (□ a)) (e : CExt Γ ΓL ΓR)
    → unbox t e ≈ unbox (substTm (factorSubₛ e idₛ) t) (factorExtₛ e idₛ)
  fact-unbox≈ {a = a} {Γ = Γ} t e = begin
    unbox t e
      -- expand extension e
      ≡⟨ cong-unbox2≡ ⟩
    unbox t (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))
      -- apply shift-unbox
      ≈⟨ ⟶-to-≈ (shift-unbox _ _ _) ⟩
    unbox (wkTm (LFExtToWk (factorSubₛIdWk e)) t) (factorExtₛ e idₛ)
      -- rewrite wkTm to substTm
      ≈⟨ cong-unbox≈ (coh-wkTm-substTm t _) ⟩
    unbox (substTm (embWk (LFExtToWk (factorSubₛIdWk e))) t) (factorExtₛ e idₛ)
      -- show that the subst is the factorisation of the id subst
      ≡˘⟨ cong1 unbox (cong1 substTm {y = t} (factorSubₛIdWkIsFactorSubₛId e)) ⟩
    unbox (substTm (factorSubₛ e idₛ) t) (factorExtₛ e idₛ) ∎
    where
    open SetoidReasoning (Tm-setoid Γ a)

rightIdSub : (s : Sub Γ Γ') → s ≈ₛ s ∙ₛ idₛ
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
      ≡⟨ cong-lock2≡ ⟩
    lock s (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))
      -- apply shift-lock≈ₛ
      ≈⟨ shift-lock≈ₛ _ ⟩
    lock (wkSub (LFExtToWk (factorSubₛIdWk e)) s) (factorExtₛ e idₛ)
      -- apply IH
      ≈⟨ cong-lock≈ₛ (wkSubPres≈ _ (rightIdSub s)) ⟩
    lock (wkSub (LFExtToWk (factorSubₛIdWk e)) (s ∙ₛ idₛ)) (factorExtₛ e idₛ)
      -- rewrite using coherence between weakening and composing substs (associativity, really)
      ≡⟨ cong1 lock (coh-wkSub-∙ₛ s idₛ (LFExtToWk (factorSubₛIdWk e))) ⟩
    lock (s ∙ₛ wkSub (LFExtToWk (factorSubₛIdWk e)) idₛ) (factorExtₛ e idₛ)
      --  weakening of id subst is itself a weakening
      ≡⟨ cong1 lock (cong (s ∙ₛ_) (wkSubId _)) ⟩
    lock (s ∙ₛ embWk (LFExtToWk (factorSubₛIdWk e))) (factorExtₛ e idₛ)
      -- show that the weakening subst is the factorisation of the id subst
      ≡˘⟨ cong1 lock (cong (s ∙ₛ_) (factorSubₛIdWkIsFactorSubₛId e)) ⟩
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
    h nil        σ⟶ₛσ'                   t = cong-unbox≈′ (substTmPres⟶ t σ⟶ₛσ')
    h (ext e)    (cong-`,⟶ₛ1 σ⟶σ')       t = h e σ⟶σ' t
    h (ext e)    (cong-`,⟶ₛ2 t≈t')       t = cong-unbox2≈
    h (ext#- e) (cong-lock⟶ₛ σ⟶σ')       t = h e σ⟶σ' t
    h (ext#- e) (shift-lock⟶ₛ {s = σ} w) t {e'} {e''} = let open SetoidReasoning (Tm-setoid _ _) in
        begin
          unbox (substTm (factorSubₛ e σ) t) e'
        ≈⟨ shift-unbox≈ (substTm (factorSubₛ e σ) t) (factorDropsWk (factorExtₛ e σ) w) ⟩
          unbox (wkTm (LFExtToWk (factorDropsWk (factorExtₛ e σ) w)) (substTm (factorSubₛ e σ) t)) (subst1 (CExt _) (lCtxₛ-wkSub-comm e σ (LFExtToWk w)) e'')
        ≡⟨ cong (λ w' → unbox (wkTm w' _) (subst1 (CExt _) (lCtxₛ-wkSub-comm e σ (LFExtToWk w)) e'')) (factorDropsWkIsfactorWk (factorExtₛ e σ) w) ⟩
          unbox (wkTm (factorWk (factorExtₛ e σ) (LFExtToWk w)) (substTm (factorSubₛ e σ) t)) (subst1 (CExt _) (lCtxₛ-wkSub-comm e σ (LFExtToWk w)) e'')
        ≡˘⟨ cong1 unbox (nat-substTm t (factorSubₛ e σ) (factorWk (factorExtₛ e σ) (LFExtToWk w))) ⟩
          unbox (substTm (wkSub (factorWk (factorExtₛ e σ) (LFExtToWk w)) (factorSubₛ e σ)) t) (subst1 (CExt _) (lCtxₛ-wkSub-comm e σ (LFExtToWk w)) e'')
        ≡˘⟨ dcong₃ (λ _Δ s e → unbox (substTm s t) e) (lCtxₛ-wkSub-comm e σ (LFExtToWk w)) (factorSubₛ-wkSub-comm e σ (LFExtToWk w)) refl ⟩
          unbox (substTm (factorSubₛ e (wkSub (LFExtToWk w) σ)) t) e''
        ∎

-- XXX: fold
substTmPres≈ : (t : Tm Γ a) → (σ≈σ' : σ ≈ₛ σ') → substTm σ t ≈ substTm σ' t
substTmPres≈ t ε                    = ≈-refl
substTmPres≈ t (inj₁ σ⟶σ' ◅ σ'≈σ'') = ≈-trans (substTmPres⟶ t σ⟶σ') (substTmPres≈ t σ'≈σ'')
substTmPres≈ t (inj₂ σ'⟶σ ◅ σ≈σ'')  = ≈-˘trans (substTmPres⟶ t σ'⟶σ) (substTmPres≈ t σ≈σ'')
