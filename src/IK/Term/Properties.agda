{-# OPTIONS --safe --without-K #-}
module IK.Term.Properties where

-- Welcome to the hell of mind-numbing syntactic lemmas.
-- No good ever comes from proving these lemmas, but no
-- good can happen without proving them.

open import Data.Product using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; subst-application)

open import PEUtil

open import IK.Term.Base
open import IK.Term.Reduction

--------------------
-- Substitution laws
--------------------

-- NOTE: these are only the laws that follow directly from the structure of substitutions
coh-trimSub-wkVar : (x : Var Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substVar (trimSub w s) x ≡ substVar s (wkVar w x)
coh-trimSub-wkVar zero     (s `, x)  (drop w)
  = coh-trimSub-wkVar zero s w
coh-trimSub-wkVar zero     (s `, x)  (keep w)
  = refl
coh-trimSub-wkVar (succ x) (s `, x₁) (drop w)
  = coh-trimSub-wkVar (succ x) s w
coh-trimSub-wkVar (succ x) (s `, x₁) (keep w)
  = coh-trimSub-wkVar x s w

-- `trimSub` preserves the identity
trimSubPresId : (s : Sub Δ Γ) → trimSub idWk s ≡ s
trimSubPresId []         = refl
trimSubPresId (s `, x)   = cong (_`, _) (trimSubPresId s)
trimSubPresId (lock s x) = cong₂ lock (trimSubPresId s) refl

-- naturality of substVar
nat-substVar : (x : Var Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substVar (wkSub w s) x ≡ wkTm w (substVar s x)
nat-substVar zero     (s `, t) w = refl
nat-substVar (succ x) (s `, t) w = nat-substVar x s w

-- naturality of trimSub
nat-trimSub : (s : Sub Γ Δ) (w : Δ' ⊆ Δ) (w' : Γ ⊆ Γ')
  → wkSub w' (trimSub w s) ≡ trimSub w (wkSub w' s)
nat-trimSub []         base      w' = refl
nat-trimSub (s `, t)   (drop w)  w' = nat-trimSub s w w'
nat-trimSub (s `, t)   (keep w)  w' = cong (_`, wkTm w' t) (nat-trimSub s w w')
nat-trimSub (lock s x) (keep# w) w' = cong₂ lock (nat-trimSub s w _) refl

-- `trimSub` on the identity substitution embeds the weakening
trimSubId : (w : Γ ⊆ Δ) → trimSub w idₛ ≡ embWk w
trimSubId base      = refl
trimSubId (drop w)  = trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w))
trimSubId (keep w)  = cong (_`, var zero) (trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w)))
trimSubId (keep# w) = cong₂ lock (trimSubId w) refl

---------------
-- Functor laws
---------------

-- Standard, standard, standard, oh wait...

wkTmPresId : (t : Tm Γ a) → wkTm idWk t ≡ t
wkTmPresId (var   v)   = cong  var (wkVarPresId v)
wkTmPresId (lam   t)   = cong  lam (wkTmPresId  t)
wkTmPresId (app   t u) = cong₂ app (wkTmPresId  t) (wkTmPresId u)
wkTmPresId (box   t)   = cong  box (wkTmPresId  t)
wkTmPresId (unbox t e) with ←#IsPre# e | #→IsPost# e
wkTmPresId (unbox t e) | refl | refl = cong₂ unbox
  (trans (cong₂ wkTm (sliceLeftId e) refl) (wkTmPresId t))
  (wkLFExtPresId e)

wkSubPresId : (s : Sub Γ Δ) → wkSub idWk s ≡ s
wkSubPresId []       = refl
wkSubPresId (s `, t) = cong₂ _`,_ (wkSubPresId s) (wkTmPresId t)
wkSubPresId (lock s e) with ←#IsPre# e | #→IsPost# e
... | refl | refl = cong₂ lock
  (trans (cong₂ wkSub (sliceLeftId e) refl) (wkSubPresId s))
  (wkLFExtPresId e)

-- weakening of terms (a functor map) preserves weakening composition
wkTmPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (t : Tm Γ a)
  → wkTm w' (wkTm w t) ≡ wkTm (w ∙ w') t
wkTmPres∙ w w' (var   v)   = cong  var (wkVarPres∙ w w' v)
wkTmPres∙ w w' (lam   t)   = cong  lam (wkTmPres∙ (keep w) (keep  w') t)
wkTmPres∙ w w' (app   t u) = cong₂ app (wkTmPres∙ w w' t) (wkTmPres∙ w w' u)
wkTmPres∙ w w' (box   t)   = cong  box (wkTmPres∙ (keep# w) (keep# w') t)
wkTmPres∙ w w' (unbox t e) = cong₂ unbox
  (trans (wkTmPres∙ _ _ _) (cong₂ wkTm (sliceLeftPres∙ w w' e) refl)) (wkLFExtPres∙  w w' e)

-- weakening of substitutions preserves weakening compisition
wkSubPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (s : Sub Γ ΓR)
  → wkSub w' (wkSub w s) ≡ wkSub (w ∙ w') s
wkSubPres∙ w w' []         = refl
wkSubPres∙ w w' (s `, t)   = cong₂ _`,_ (wkSubPres∙ w w' s) (wkTmPres∙ w w' t)
wkSubPres∙ w w' (lock s e) = cong₂ lock
  (trans  (wkSubPres∙ _ _ s) (cong₂ wkSub (sliceLeftPres∙ w w' e) refl))
  (wkLFExtPres∙ w w' e)

private
  wkSubFreshLemma : {s : Sub Δ Γ} {w : Δ ⊆ Δ'}
    → wkSub fresh[ a ] (wkSub w s) ≡ wkSub (keep w) (dropₛ s)
  wkSubFreshLemma {s = s} {w} = trans (wkSubPres∙ w fresh s) (trans
    (cong₂ wkSub (cong drop (rightIdWk _)) refl )
    (sym (trans
      (wkSubPres∙ _ _ _)
      (cong₂ wkSub (cong drop (leftIdWk _)) refl))))

nat-subsTm : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
nat-subsTm (var x)           s          w
  = nat-substVar x s w
nat-subsTm (lam {Γ} {a} t)   s          w
  = cong lam
    (trans (cong (λ s → substTm (s `, var zero) t) wkSubFreshLemma)
    (nat-subsTm t (keepₛ s) (keep w)))
nat-subsTm (app t u)         s          w
  = cong₂ app (nat-subsTm t s w) (nat-subsTm u s w)
nat-subsTm (box t)           s          w
  = cong box (nat-subsTm t (lock s nil) (keep# w))
nat-subsTm (unbox t nil)     (lock s x) w
  = cong₂ unbox (nat-subsTm t s _) refl
nat-subsTm (unbox t (ext x)) (s `, _)   w
  = nat-subsTm (unbox t x) s w

-- weakening a substitution composition is the same as weakening the first sub
-- (s ∙ₛ s') ₛ∙ₑ w ≡ s ∙ₛ (s' ₛ∙ₑ w)
coh-wkSub-∙ₛ  : {Δ'' : Ctx} (s : Sub Δ Γ) (s' : Sub Δ' Δ) (w : Δ' ⊆ Δ'')
         → wkSub w (s ∙ₛ s') ≡ s ∙ₛ (wkSub w s')
coh-wkSub-∙ₛ []           s'             w
  = refl
coh-wkSub-∙ₛ (s `, x)     s'             w
  = cong₂ _`,_  (coh-wkSub-∙ₛ s s' w) (sym (nat-subsTm x s' w))
coh-wkSub-∙ₛ (lock s nil) (lock s' x)    w
  = cong₂ lock (coh-wkSub-∙ₛ s s' _) refl
coh-wkSub-∙ₛ (lock s (ext x)) (s' `, x₁) w
  = coh-wkSub-∙ₛ (lock s x) s' w

-- applying a trimmed substitution is the same as weakening and substituting
coh-trimSub-wkTm : (t : Tm Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substTm (trimSub w s) t ≡ substTm s (wkTm w t)
coh-trimSub-wkTm (var x)           s          w
  = coh-trimSub-wkVar x s w
coh-trimSub-wkTm (lam t)           s          w
  = cong lam (trans
    (cong (λ p → substTm (p `, var zero) t) (nat-trimSub s w fresh))
    (coh-trimSub-wkTm t (keepₛ s) (keep w)))
coh-trimSub-wkTm (app t u)         s          w
  = cong₂ app (coh-trimSub-wkTm t s w) (coh-trimSub-wkTm u s w)
coh-trimSub-wkTm (box t)           s          w
  = cong box (coh-trimSub-wkTm t (lock s nil) (keep# w))
coh-trimSub-wkTm (unbox t nil)     (s `, x)   (drop w)
  = coh-trimSub-wkTm (unbox t nil) s w
coh-trimSub-wkTm (unbox t (ext e)) (s `, x)   (drop w)
  = coh-trimSub-wkTm (unbox t (ext e)) s w
coh-trimSub-wkTm (unbox t (ext e)) (s `, x)   (keep w)
  = coh-trimSub-wkTm (unbox t e) s w
coh-trimSub-wkTm (unbox t nil)     (lock s x) (keep# w)
  = cong₂ unbox (coh-trimSub-wkTm t s w) refl

-- trimming the first sub in a composition is the same as weakening the second
-- s ∙ₛ (w ₑ∙ₛ s') ≡ (s ₛ∙ₑ w) ∙ₛ s'
coh-trimSub-wkSub  : {Δ₁ : Ctx} (s : Sub Δ Γ) (s' : Sub Δ₁ Δ') (w : Δ ⊆ Δ')
         → s ∙ₛ (trimSub w s') ≡ (wkSub w s) ∙ₛ s'
coh-trimSub-wkSub []               s'          w
  = refl
coh-trimSub-wkSub (s `, x)         s'          w
  = cong₂ _`,_ (coh-trimSub-wkSub s s' w) (coh-trimSub-wkTm x s' w)
coh-trimSub-wkSub (lock s nil)     (s' `, x)   (drop w)
  = coh-trimSub-wkSub (lock s nil) s' w
coh-trimSub-wkSub (lock s nil)     (lock s' x) (keep# w)
  = cong₂ lock (coh-trimSub-wkSub s s' w) refl
coh-trimSub-wkSub (lock s (ext e)) (s' `, x₁)  (drop w)
  = coh-trimSub-wkSub (lock s (ext e)) s' w
coh-trimSub-wkSub (lock s (ext x)) (s' `, x₁)  (keep w)
  = coh-trimSub-wkSub (lock s x) s' w

-- parallel substitution (substVar) preserves substitution composition
substVarPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substTm s' (substVar s x) ≡ substVar (s ∙ₛ s') x
substVarPres∙ (s `, x) s' zero      = refl
substVarPres∙ (s `, x) s' (succ x₁) = substVarPres∙ s s' x₁

private
  dropKeepLemma : (s' : Sub Δ' Δ) (s : Sub Γ Δ')
           →  dropₛ (s' ∙ₛ s) ≡ dropₛ {a = a} s' ∙ₛ keepₛ s
  dropKeepLemma s' s = trans (coh-wkSub-∙ₛ s' s fresh)
    (trans
      ((cong (s' ∙ₛ_) (sym (trimSubPresId (dropₛ s)))))
      (coh-trimSub-wkSub s' (keepₛ s) fresh))

substVarPresId : (x : Var Γ a) → substVar idₛ x ≡ var x
substVarPresId zero     = refl
substVarPresId (succ x) = trans (nat-substVar x idₛ fresh) (trans
  (cong (wkTm fresh) (substVarPresId x))
  (cong var (wkIncr x)))

module _ {e : LFExt Δ (Γ #) ΓR} {e' : LFExt Δ (Γ' #) ΓR'} where
  cong-unbox≡ : (Γ≡Γ' : Γ ≡ Γ')
    → (t≡t' : subst (λ Γ → Tm Γ (□ a)) Γ≡Γ' t ≡ t')
    → unbox t e ≡ unbox t' e'
  cong-unbox≡ Γ≡Γ' t≡t' =
    idcong₄ unbox Γ≡Γ' (extRUniq′ (cong _# Γ≡Γ') e e') t≡t' (ExtIsProp _ _)

cong-unbox≡1 : (Γ≡Γ' : Γ ≡ Γ')
  → (t≡t' : subst (λ Γ → Tm Γ (□ a)) Γ≡Γ' t ≡ t')
  → unbox t e ≡ unbox t' e'
cong-unbox≡1 = cong-unbox≡

cong-unbox≡2 : unbox t e ≡ unbox t e'
cong-unbox≡2 = cong-unbox≡ refl refl

module _ {Γ : Ctx} {a : Ty} where
  unbox-natural : (t : Tm Γ (□ a))
    → (e : LFExt Δ (Γ #) ΓR)
    → (w : LFExt Δ' Δ ΔR)
    → unbox t (e ∙Ext w) ≡ wkTm (LFExtToWk w) (unbox t e)
  unbox-natural t e w with ←#IsPre# e | #→IsPost# e
  unbox-natural t e w | refl | refl = cong-unbox≡ (←#IsPre# w)
    (trans (cong˘ (subst (λ Γ → Tm Γ (□ a)) (←#IsPre# w)) (wkTmPresId t))
      (trans (subst-application′ (Γ ⊆_) (λ w → wkTm w t) (←#IsPre# w))
        (cong˘ (λ w → wkTm w t) (sliceLeftDrop e w))))

unbox-universal : (t : Tm Γ (□ a))
  → (e : LFExt Δ (Γ #) ΓR)
  → unbox t e ≡ wkTm (LFExtToWk e) (unbox t new)
unbox-universal t e = trans cong-unbox≡2 (unbox-natural t new e)

substTmPresId : (t : Tm Γ a) → substTm idₛ t ≡ t
substTmPresId (var x)       = substVarPresId x
substTmPresId (lam t)       = cong lam (substTmPresId t)
substTmPresId (app t u)     = cong₂ app (substTmPresId t) (substTmPresId u)
substTmPresId (box t)       = cong box (substTmPresId t)
substTmPresId (unbox t nil) = cong₂ unbox (substTmPresId t) refl
substTmPresId {Γ = Γ `, a} (unbox t (ext e)) with ←#IsPre# e | #→IsPost# e | substTmPresId (unbox t e)
... | refl | refl | rec = trans (nat-subsTm (unbox t e) idₛ fresh)
    (trans˘
      (cong (wkTm fresh) rec)
      (unbox-natural t e (ext nil)))

-- NOTE: the `rec` here is a hack required for/after the 2.6.1 update
-- c.f. "Termination checking" in http://hackage.haskell.org/package/Agda-2.6.1/changelog

-- parallel substitution (substTm) preserves substitution composition
substTmPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm s' (substTm s t) ≡ substTm (s ∙ₛ s') t
substTmPres∙ s s'             (var x)
  = substVarPres∙ s s' x
substTmPres∙ s s'             (lam t)
  = cong lam
    (trans (substTmPres∙ _ _ t)
    (cong ((λ s → substTm (s `, var zero) t)) (sym (dropKeepLemma s s'))))
substTmPres∙ s s'             (app t u)
  = cong₂ app (substTmPres∙ s s' t) (substTmPres∙ s s' u)
substTmPres∙ s s'             (box t)
  = cong box (substTmPres∙ (lock s nil) (lock s' nil) t)
substTmPres∙ (lock s nil)     (lock s' nil) (unbox t nil)
  = cong₂ unbox (substTmPres∙ s s' t) refl
substTmPres∙ (lock s nil)     (lock s' (ext x)) (unbox t nil)
  = cong₂ unbox (substTmPres∙ s s' t) refl
substTmPres∙ (lock s (ext e)) (s' `, _) (unbox t nil)
  = substTmPres∙ (lock s e) s' (unbox t nil)
substTmPres∙ (lock s nil) (lock s' _) (unbox t nil)
  = cong₂ unbox (substTmPres∙ s s' t) refl
substTmPres∙ (s `, e) s' (unbox t (ext e'))
  = substTmPres∙ s s' (unbox t e')

rightIdSub : (s : Sub Γ Γ') → s ∙ₛ idₛ ≡ s
rightIdSub []           = refl
rightIdSub (s `, t)     = cong₂ _`,_ (rightIdSub s) (substTmPresId t)
rightIdSub (lock s nil) = cong₂ lock (rightIdSub s) refl
rightIdSub (lock s (ext e)) with ←#IsPre# e | #→IsPost# e
... | refl | refl = trans
  (sym (coh-wkSub-∙ₛ (lock s e) _ _))
  (trans
    (cong (wkSub fresh) (rightIdSub (lock s e)))
    (trans
      (cong₂ lock (cong₂ wkSub (sliceLeftId e) refl) (cong ext (wkLFExtPresId e)))
      (cong₂ lock (wkSubPresId s) refl)))


-- substitution composition is associative
assocSub : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (s3 : Sub Γ3 Γ4) (s2 : Sub Γ2 Γ3) → (s1 : Sub Γ1 Γ2)
  → (s3 ∙ₛ s2) ∙ₛ s1 ≡ s3 ∙ₛ (s2 ∙ₛ s1)
assocSub []                s2         s1
  = refl
assocSub (s3 `, t)         s2         s1
  = cong₂ _`,_ (assocSub s3 s2 s1) (substTmPres∙ s2 s1 t)
assocSub (lock s3 nil)     (lock s2 nil)     (lock s1 e)
  = cong (λ p → lock p e) (assocSub s3 s2 s1)
assocSub (lock s3 nil)     (lock s2 (ext e)) (s1 `, _)
  = assocSub (lock s3 nil) (lock s2 e) s1
assocSub (lock s3 (ext e)) (s2 `, _) s1
  = assocSub (lock s3 e) s2 s1


private
  -- just a helper to reduce redundancy, nothing too interesting
  auxLemma : (w : Γ ⊆ Δ) → wkSub (drop[ a ] (w ∙ idWk)) idₛ ≡ dropₛ (embWk w)

wkSubId : (w : Γ ⊆ Δ) → wkSub w idₛ ≡ embWk w

auxLemma w = (trans
    (sym (wkSubPres∙ w fresh idₛ))
    (cong (wkSub fresh) (wkSubId w)))

wkSubId base      = refl
wkSubId (drop w)  = trans
  (cong (λ w' → wkSub (drop w') idₛ) (sym (rightIdWk w)))
  (auxLemma w)
wkSubId (keep w)  = cong (_`, var zero) (trans
  (wkSubPres∙ fresh (keep w) idₛ)
  (trans
    (cong₂ wkSub (cong drop (trans (leftIdWk _) (sym (rightIdWk _)))) refl)
    (auxLemma w)))
wkSubId (keep# w) = cong₂ lock (wkSubId w) refl

-- Outcast lemmas

keepFreshLemma : {w : Γ ⊆ Γ'} {t : Tm Γ a}
  → wkTm fresh[ b ] (wkTm w t) ≡ wkTm (keep w) (wkTm fresh t)
keepFreshLemma = trans (wkTmPres∙ _ _ _) (sym (trans
    (wkTmPres∙ _ _ _)
    (cong₂ wkTm (cong drop (trans (leftIdWk _) (sym (rightIdWk _)))) refl)))

sliceCompLemma : (w : Γ ⊆ Δ) (e : LFExt Γ (ΓL #) ΓR) (t : Tm (ΓL #) a)
  → wkTm (LFExtToWk (wkLFExt e w)) (wkTm (keep# (sliceLeft e w)) t) ≡
      wkTm w (wkTm (LFExtToWk e) t)
sliceCompLemma w e t = (trans (wkTmPres∙ _ _ _) (sym (trans
  (wkTmPres∙ _ _ _)
  (cong₂ wkTm (slicingLemma w e) refl))))

beta-wk-lemma : (w  : Γ ⊆ Δ) (u : Tm Γ a) (t : Tm (Γ `, a) b)
  → substTm (idₛ `, wkTm w u) (wkTm (keep w) t) ≡ wkTm w (substTm (idₛ `, u) t)
beta-wk-lemma w u t = trans
  (sym (coh-trimSub-wkTm t _ (keep w)))
  (sym (trans
    (sym (nat-subsTm t _ _))
    (cong
      (λ p → substTm (p `, wkTm w u) t)
      (sym (trans (trimSubId w) (sym (wkSubId w)))))))

-----------------------------------
--- Reduction and conversion lemmas
-----------------------------------

wkTmPres⟶ :  {t t' : Tm Γ a}
  → (w : Γ ⊆ Δ)
  → t ⟶ t'
  → wkTm w t ⟶ wkTm w t'
wkTmPres⟶ w (red-fun {t = t} {u = u})
  = step-≡ red-fun (beta-wk-lemma w u t)
wkTmPres⟶ w exp-fun
  = step-≡ exp-fun (cong lam (cong₂ app keepFreshLemma refl))
wkTmPres⟶ w (red-box {e = e})
  = step-≡ red-box (sliceCompLemma w e _)
wkTmPres⟶ w exp-box
  = exp-box
wkTmPres⟶ w (cong-lam r)
  = cong-lam (wkTmPres⟶ (keep w) r)
wkTmPres⟶ w (cong-box r)
  = cong-box (wkTmPres⟶ (keep# w) r)
wkTmPres⟶ w (cong-unbox r)
  = cong-unbox (wkTmPres⟶ (sliceLeft _ w) r)
wkTmPres⟶ w (cong-app1 r)
  = cong-app1 (wkTmPres⟶ w r)
wkTmPres⟶ w (cong-app2 r)
  = cong-app2 (wkTmPres⟶ w r)

wkTmPres⟶* :  {t t' : Tm Γ a}
  → (w : Γ ⊆ Δ)
  → t ⟶* t'
  → wkTm w t ⟶* wkTm w t'
wkTmPres⟶* w = cong-⟶-to-cong-⟶* (wkTmPres⟶ w)
