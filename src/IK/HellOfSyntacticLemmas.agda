module IK.HellOfSyntacticLemmas where

-- Welcome to the hell of mind-numbing syntactic lemmas.
-- No good ever comes from proving these lemmas, but no
-- good can happen without proving them.

open import Data.Product  using (Σ ; _×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality

open import IK.Term
open import IK.Norm

---------------
-- Functor laws
---------------

-- Standard, standard, standard, oh wait...

wkTmPresId : (t : Tm Γ a) → wkTm idWk t ≡ t
wkTmPresId (var x) = cong var (wkVarPresId x)
wkTmPresId (lam t) = cong lam (wkTmPresId t)
wkTmPresId (app t u) = cong₂ app (wkTmPresId t) (wkTmPresId u)
wkTmPresId (box t) = cong box (wkTmPresId t)
wkTmPresId (unbox t e) with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
wkTmPresId (unbox t e) | refl | refl = cong₂ unbox
  (trans (cong₂ wkTm (stashWkId e) refl) (wkTmPresId t))
  (resExtId e)

wkSubPresId : (s : Sub Γ Δ) → wkSub idWk s ≡ s
wkSubPresId [] = refl
wkSubPresId (s `, t) = cong₂ _`,_ (wkSubPresId s) (wkTmPresId t)
wkSubPresId (lock s e) with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
... | refl | refl = cong₂ lock
  (trans (cong₂ wkSub (stashWkId e) refl) (wkSubPresId s))
  (resExtId e)

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var x)     = cong var (wkVarPresId x)
wkNePresId (app n m)   = cong₂ app (wkNePresId n) (wkNfPresId m)
wkNePresId (unbox n e) with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
... | refl | refl = cong₂ unbox
  (trans (cong₂ wkNe (stashWkId e) refl) (wkNePresId n))
  (resExtId e)

wkNfPresId (up𝕓 n) = cong up𝕓 (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

-- weakening of terms (a functor map) preserves weakening composition
wkTmPres∙ : (w : Γ' ≤ Γ) (w' : Δ ≤ Γ') (t : Tm Γ a)
  → wkTm w' (wkTm w t) ≡ wkTm (w ∙ w') t
wkTmPres∙ w w' (var x)   = cong var (wkVarPres∙ w w' x)
wkTmPres∙ w w' (lam t)   = cong lam (wkTmPres∙ (keep w) (keep w') t)
wkTmPres∙ w w' (app t u) = cong₂ app (wkTmPres∙ w w' t) (wkTmPres∙ w w' u)
wkTmPres∙ w w' (box t)   = cong box (wkTmPres∙ (keep🔒 w) (keep🔒 w') t)
wkTmPres∙ w w' (unbox t e) = cong₂ unbox
  (trans (wkTmPres∙ _ _ _) (cong₂ wkTm (stashSquash w' w e) refl)) (resAccLem w' w e)

-- weakening of substitutions preserves weakening compisition
wkSubPres∙ : (w : Γ' ≤ Γ) (w' : Δ ≤ Γ') (s : Sub Γ ΓR)
  → wkSub w' (wkSub w s) ≡ wkSub (w ∙ w') s
wkSubPres∙ w w' []       = refl
wkSubPres∙ w w' (s `, t) = cong₂ _`,_ (wkSubPres∙ w w' s) (wkTmPres∙ w w' t)
wkSubPres∙ w w' (lock s e) = cong₂ lock
  (trans  (wkSubPres∙ _ _ s) (cong₂ wkSub (stashSquash w' w e) refl))
  (resAccLem w' w e)

wkNePres∙ : (w : Γ' ≤ Γ) (w' : Δ ≤ Γ') (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ' ≤ Γ) (w' : Δ ≤ Γ') (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkNePres∙ w w' (app n m)   = cong₂ app (wkNePres∙ w w' n) (wkNfPres∙ w w' m)
wkNePres∙ w w' (unbox n e) = cong₂ unbox
  (trans (wkNePres∙ _ _ _) (cong₂ wkNe (stashSquash w' w e) refl)) (resAccLem w' w e)

wkNfPres∙ w w' (up𝕓 n) = cong up𝕓 (wkNePres∙ w w' n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep w) (keep w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep🔒 w) (keep🔒 w') n)


private
  wkSubFreshLemma : {s : Sub Δ Γ} {w : Δ' ≤ Δ}
    → wkSub (fresh {a = a}) (wkSub w s) ≡ wkSub (keep w) (dropₛ s)
  wkSubFreshLemma {s = s} {w} = trans (wkSubPres∙ w fresh s) (trans
    (cong₂ wkSub (cong drop (rightIdWk _)) refl )
    (sym (trans
      (wkSubPres∙ _ _ _)
      (cong₂ wkSub (cong drop (leftIdWk _)) refl))))

nat-subsTm : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ' ≤ Δ)
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
nat-subsTm (var x)           s          w
  = nat-substVar x s w
nat-subsTm (lam {Γ} {a} t)   s          w
  = cong lam
    (trans (cong (λ s → substTm (s `, var ze) t) wkSubFreshLemma)
    (nat-subsTm t (keepₛ s) (keep w)))
nat-subsTm (app t u)         s          w
  = cong₂ app (nat-subsTm t s w) (nat-subsTm u s w)
nat-subsTm (box t)           s          w
  = cong box (nat-subsTm t (lock s nil) (keep🔒 w))
nat-subsTm (unbox t nil)     (lock s x) w
  = cong₂ unbox (nat-subsTm t s _) refl
nat-subsTm (unbox t (ext x)) (s `, _)   w
  = nat-subsTm (unbox t x) s w

-- weakening a substitution composition is the same as weakening the first sub
-- (s ∙ₛ s') ₛ∙ₑ w ≡ s ∙ₛ (s' ₛ∙ₑ w)
coh-wkSub-∙ₛ  : {Δ'' : Ctx} (s : Sub Δ Γ) (s' : Sub Δ' Δ) (w : Δ'' ≤ Δ')
         → wkSub w (s ∙ₛ s') ≡ s ∙ₛ (wkSub w s')
coh-wkSub-∙ₛ [] s' w
  = refl
coh-wkSub-∙ₛ (s `, x) s' w
  = cong₂ _`,_  (coh-wkSub-∙ₛ s s' w) (sym (nat-subsTm x s' w))
coh-wkSub-∙ₛ (lock s nil) (lock s' x) w
  = cong₂ lock (coh-wkSub-∙ₛ s s' _) refl
coh-wkSub-∙ₛ (lock s (ext x)) (s' `, x₁) w
  = coh-wkSub-∙ₛ (lock s x) s' w

-- applying a trimmed substitution is the same as weakening and substituting
coh-trimSub-wkTm : (t : Tm Γ a) (s : Sub Δ' Δ) (w : Δ ≤ Γ)
  → substTm (trimSub w s) t ≡ substTm s (wkTm w t)
coh-trimSub-wkTm (var x) s w
  = coh-trimSub-wkVar x s w
coh-trimSub-wkTm (lam t) s w
  = cong lam (trans
    (cong (λ p → substTm (p `, var ze) t) (nat-trimSub s w fresh))
    (coh-trimSub-wkTm t (keepₛ s) (keep w)))
coh-trimSub-wkTm (app t u) s w
  = cong₂ app (coh-trimSub-wkTm t s w) (coh-trimSub-wkTm u s w)
coh-trimSub-wkTm (box t) s w
  = cong box (coh-trimSub-wkTm t (lock s nil) (keep🔒 w))
coh-trimSub-wkTm (unbox t nil) (s `, x) (drop w)
  = coh-trimSub-wkTm (unbox t nil) s w
coh-trimSub-wkTm (unbox t (ext e)) (s `, x) (drop w)
  = coh-trimSub-wkTm (unbox t (ext e)) s w
coh-trimSub-wkTm (unbox t (ext e))   (s `, x) (keep w)
  = coh-trimSub-wkTm (unbox t e) s w
coh-trimSub-wkTm (unbox t nil) (lock s x) (keep🔒 w)
  = cong₂ unbox (coh-trimSub-wkTm t s w) refl

-- trimming the first sub in a composition is the same as weakening the second
-- s ∙ₛ (w ₑ∙ₛ s') ≡ (s ₛ∙ₑ w) ∙ₛ s'
coh-trimSub-wkSub  : {Δ₁ : Ctx} (s : Sub Δ Γ) (s' : Sub Δ₁ Δ') (w : Δ' ≤ Δ)
         → s ∙ₛ (trimSub w s') ≡ (wkSub w s) ∙ₛ s'
coh-trimSub-wkSub []       s' w
  = refl
coh-trimSub-wkSub (s `, x) s' w
  = cong₂ _`,_ (coh-trimSub-wkSub s s' w) (coh-trimSub-wkTm x s' w)
coh-trimSub-wkSub (lock s nil) (s' `, x) (drop w)
  = coh-trimSub-wkSub (lock s nil) s' w
coh-trimSub-wkSub (lock s nil) (lock s' x) (keep🔒 w)
  = cong₂ lock (coh-trimSub-wkSub s s' w) refl
coh-trimSub-wkSub (lock s (ext e)) (s' `, x₁) (drop w)
  = coh-trimSub-wkSub (lock s (ext e)) s' w
coh-trimSub-wkSub (lock s (ext x)) (s' `, x₁) (keep w)
  = coh-trimSub-wkSub (lock s x) s' w

-- parallel substitution (substVar) preserves substitution composition
substVarPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (x : Var Γ a)
  → substTm s' (substVar s x) ≡ substVar (s ∙ₛ s') x
substVarPres∙ (s `, x) s' ze      = refl
substVarPres∙ (s `, x) s' (su x₁) = substVarPres∙ s s' x₁

private
  dropKeepLemma : (s' : Sub Δ' Δ) (s : Sub Γ Δ')
           →  dropₛ (s' ∙ₛ s) ≡ dropₛ {a = a} s' ∙ₛ keepₛ s
  dropKeepLemma s' s = trans (coh-wkSub-∙ₛ s' s fresh)
    (trans
      ((cong (s' ∙ₛ_) (sym (trimSubPresId (dropₛ s)))))
      (coh-trimSub-wkSub s' (keepₛ s) fresh))

substVarPresId : (x : Var Γ a) → substVar idₛ x ≡ var x
substVarPresId ze = refl
substVarPresId (su x) = trans (nat-substVar x idₛ fresh) (trans
  (cong (wkTm fresh) (substVarPresId x))
  (cong var (wkIncr x)))

private
  dropUnboxLemma : (e  : LFExt Γ (ΓL 🔒) ΓR) {t : Tm ΓL (◻ a)}
    → wkTm (fresh {a = b}) (unbox t e) ≡ unbox t (ext e)
  dropUnboxLemma e with (←🔒IsPre🔒 e) | 🔒→isPost🔒 e
  dropUnboxLemma e | refl | refl = cong₂ unbox (trans
    (cong₂ wkTm (stashWkId e) refl) (wkTmPresId _))
    (cong ext (resExtId e))

substTmPresId : (t : Tm Γ a) → substTm idₛ t ≡ t
substTmPresId (var x) = substVarPresId x
substTmPresId (lam t) = cong lam (substTmPresId t)
substTmPresId (app t u) = cong₂ app (substTmPresId t) (substTmPresId u)
substTmPresId (box t) = cong box (substTmPresId t)
substTmPresId (unbox t nil) = cong₂ unbox (substTmPresId t) refl
substTmPresId {Γ = Γ `, a} (unbox t (ext e)) with ←🔒IsPre🔒 e | 🔒→isPost🔒 e | substTmPresId (unbox t e)
... | refl | refl | rec = trans (nat-subsTm (unbox t e) idₛ fresh)
    (trans
      (cong (wkTm fresh) rec)
      (dropUnboxLemma e))

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
    (cong ((λ s → substTm (s `, var ze) t)) (sym (dropKeepLemma s s'))))
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
rightIdSub [] = refl
rightIdSub (s `, t) = cong₂ _`,_ (rightIdSub s) (substTmPresId t)
rightIdSub (lock s nil) = cong₂ lock (rightIdSub s) refl
rightIdSub (lock s (ext x)) with ←🔒IsPre🔒 x | 🔒→isPost🔒 x
... | refl | refl = trans
  (sym (coh-wkSub-∙ₛ (lock s x) _ _))
  (trans
    (cong (wkSub fresh) (rightIdSub (lock s x)))
    (trans
      (cong₂ lock (cong₂ wkSub (stashWkId x) refl) (cong ext (resExtId x)))
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
  auxLemma : (w : Δ ≤ Γ) → wkSub (drop {a = a} (w ∙ idWk)) idₛ ≡ dropₛ (embWk w)

wkSubId : (w : Δ ≤ Γ) → wkSub w idₛ ≡ embWk w

auxLemma w = (trans
    (sym (wkSubPres∙ w fresh idₛ))
    (cong (wkSub fresh) (wkSubId w)))

wkSubId base = refl
wkSubId (drop w) = trans
  (cong (λ w' → wkSub (drop w') idₛ) (sym (rightIdWk w)))
  (auxLemma w)
wkSubId (keep w)  = cong (_`, var ze) (trans
  (wkSubPres∙ fresh (keep w) idₛ)
  (trans
    (cong₂ wkSub (cong drop (trans (leftIdWk _) (sym (rightIdWk _)))) refl)
    (auxLemma w)))
wkSubId (keep🔒 w) = cong₂ lock (wkSubId w) refl

------------------------
-- Naturality conditions
------------------------

-- Normal forms and neutrals obey "naturality" of embeddding, i.e.,
-- weakening can be commuted with embedding.

-- the mutual brothers normal forms and neutrals who,
-- as always, must be handled (mutually) together
nat-embNe : (w : Γ' ≤ Γ) (n : Ne Γ a)
  → wkTm w (embNe n) ≡ embNe (wkNe w n)
nat-embNf : (w : Γ' ≤ Γ) (n : Nf Γ a)
  → wkTm w (embNf n) ≡ embNf (wkNf w n)

nat-embNf w (up𝕓 x) = nat-embNe w x
nat-embNf w (lam n) = cong lam (nat-embNf (keep w) n)
nat-embNf w (box n) = cong box (nat-embNf (keep🔒 w) n)

nat-embNe w (var x)     = refl
nat-embNe w (app n x)   = cong₂ app (nat-embNe w n) (nat-embNf w x)
nat-embNe w (unbox n x) = cong₂ unbox (nat-embNe (stashWk x w) n) refl

-- Outcast lemmas

keepFreshLemma : {w : Γ' ≤ Γ} {t : Tm Γ a}
  → wkTm (fresh {a = b}) (wkTm w t) ≡ wkTm (keep w) (wkTm fresh t)
keepFreshLemma = trans (wkTmPres∙ _ _ _) (sym (trans
    (wkTmPres∙ _ _ _)
    (cong₂ wkTm (cong drop (trans (leftIdWk _) (sym (rightIdWk _)))) refl)))

sliceCompLemma : (w : Δ ≤ Γ) (e : LFExt Γ (ΓL 🔒) ΓR) (t : Tm (ΓL 🔒) a)
  → wkTm (wᵣ (resExt e w)) (wkTm (keep🔒 (stashWk e w)) t) ≡
      wkTm w (wkTm (wᵣ e) t)
sliceCompLemma w e t = (trans (wkTmPres∙ _ _ _) (sym (trans
  (wkTmPres∙ _ _ _)
  (cong₂ wkTm (goodSlice w e) refl))))

beta-wk-lemma : (w  : Δ ≤ Γ) (u : Tm Γ a) (t : Tm (Γ `, a) b)
  → substTm (idₛ `, wkTm w u) (wkTm (keep w) t) ≡ wkTm w (substTm (idₛ `, u) t)
beta-wk-lemma w u t = trans
  (sym (coh-trimSub-wkTm t _ (keep w)))
  (sym (trans
    (sym (nat-subsTm t _ _))
    (cong
      (λ p → substTm (p `, wkTm w u) t)
      (sym (trans (trimSubId w) (sym (wkSubId w)))))))
