module IS4.HellOfSyntacticLemmas where

-- Welcome to the hell of mind-numbing syntactic lemmas.
-- No good ever comes from proving these lemmas, but no
-- good can happen without proving them.

open import Data.Product  using (Σ ; _×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Product.Properties using (Σ-≡,≡↔≡; ×-≡,≡↔≡)

open import Function using (Inverse)

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_)

open import IS4.Term
open import IS4.Norm

open import HEUtil

open ≡-Reasoning

-- Custom combinator to prove syntactic lemmas about unbox, lock, etc.
module _
  (T : Ctx → Set)                             -- Type of indexed sets (terms, etc.)
  (E : Ctx → Ctx → Set)                       -- Type of context extensions
  {R : {ΓL ΓR : Ctx} → T ΓL → E ΓL ΓR → Set}  -- ... (unbox, lock, etc.)
  where

  xcong : {i1 i2 j1 j2 : Ctx} →
           i1 ≡ i2 → j1 ≡ j2 →
          {t1 : T i1} {t2 : T i2} {e1 : E i1 j1} {e2 : E i2 j2}
          (unb : {i j : Ctx} → (t : T i ) (e : E i j) → R t e) →
          t1 ≅ t2 →
          e1 ≅ e2 →
          unb t1 e1 ≅ unb t2 e2
  xcong refl refl _ HE.refl HE.refl = HE.refl

wkTmPresId : (t : Tm Γ a) → wkTm idWk t ≡ t
wkTmPresId (var x)     = cong var (wkVarPresId x)
wkTmPresId (lam t)     = cong lam (wkTmPresId t)
wkTmPresId (app t u)   = cong₂ app (wkTmPresId t) (wkTmPresId u)
wkTmPresId (box t)     = cong box (wkTmPresId t)
wkTmPresId {Γ = Γ} {a = a} (unbox {ΓL = ΓL} {ΓR = ΓR} t e) = begin
  wkTm idWk (unbox t e)
    ≡⟨⟩
  unbox {ΓL = lCtx e idWk} {ΓR = rCtx e idWk} (wkTm (factorWk e idWk[ Γ ]) t) (factorExt e idWk[ Γ ])
    ≅⟨ xcong
      (λ ΓL → Tm ΓL (◻ a)) (CExt Γ)
      (lCtxPresId e) (rCtxPresId e)
      unbox
      factorWkPresId-under-wkTm
      (≡-subst₂-addable (CExt Γ) _ _ (factorExt _ _)) ⟩
  unbox {ΓL = ΓL} {ΓR = ΓR} (wkTm idWk[ ΓL ] t) (subst₂ (CExt Γ) (lCtxPresId e) (rCtxPresId e) (factorExt e idWk))
    ≡⟨ cong₂ unbox (wkTmPresId t) (factorExtPresId e) ⟩
  unbox t e ∎
    where
      factorWkPresId-under-wkTm : wkTm (factorWk e idWk) t ≅ wkTm idWk t
      factorWkPresId-under-wkTm = HE.icong (ΓL ⊆_) (lCtxPresId e) (λ w → wkTm w t)
        (HE.trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresId e)))

wkSubPresId : (s : Sub Δ Γ) → wkSub idWk s ≡ s
wkSubPresId []         = refl
wkSubPresId (s `, t)   = cong₂ _`,_ (wkSubPresId s) (wkTmPresId t)
wkSubPresId {Δ = Δ} (lock {ΔL = ΔL} {Γ = Γ} s e) = begin
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
      factorWkPresId-under-wkSub = HE.icong (ΔL ⊆_) (lCtxPresId e) (λ w → wkSub w s)
        (HE.trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresId e)))

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var x)     = cong var (wkVarPresId x)
wkNePresId (app n m)   = cong₂ app (wkNePresId n) (wkNfPresId m)
wkNePresId {Γ = Γ} (unbox {ΓL = ΓL} {a = a} n e) = begin
  wkNe idWk (unbox n e)
    ≡⟨⟩
  unbox (wkNe (factorWk e idWk) n) (factorExt e idWk)
    ≅⟨ xcong
      (λ ΓL → Ne ΓL (◻ a)) (CExt Γ)
      (lCtxPresId e) (rCtxPresId e)
      unbox
      factorWkPresId-under-wkNe
      (≡-subst₂-addable (CExt Γ) _ _ (factorExt _ _)) ⟩
  unbox (wkNe idWk n) (subst₂ (CExt Γ) (lCtxPresId e) (rCtxPresId e) (factorExt e idWk))
    ≡⟨ cong₂ unbox (wkNePresId n) (factorExtPresId e) ⟩
  unbox n e ∎
    where
      factorWkPresId-under-wkNe : wkNe (factorWk e idWk) n ≅ wkNe idWk n
      factorWkPresId-under-wkNe = HE.icong (ΓL ⊆_) (lCtxPresId e) (λ w → wkNe w n)
        (HE.trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresId e)))

wkNfPresId (up𝕓 n) = cong up𝕓 (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

wkTmPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (t : Tm Γ a)
  → wkTm w' (wkTm w t) ≡ wkTm (w ∙ w') t
wkTmPres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkTmPres∙ w w' (lam t)     = cong lam (wkTmPres∙ (keep w) (keep w') t)
wkTmPres∙ w w' (app t u)   = cong₂ app (wkTmPres∙ w w' t) (wkTmPres∙ w w' u)
wkTmPres∙ w w' (box t)     = cong box (wkTmPres∙ (keep🔒 w) (keep🔒 w') t)
wkTmPres∙ {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} w w' (unbox {ΓL = ΓL} {a = a} {ΓR = ΓR} t e) = begin
  wkTm w' (wkTm w (unbox t e))
    ≡⟨⟩
  unbox {ΓL = lCtx (factorExt e w) w'} {ΓR = rCtx (factorExt e w) w'}
    (wkTm (factorWk (factorExt e w) w') (wkTm (factorWk e w) t))
    (factorExt (factorExt e w) w')
    ≡⟨ cong₂ unbox (wkTmPres∙ _ _ t) (sym (factorExtPres∙ _ _ _)) ⟩
  unbox {ΓL = lCtx (factorExt e w) w'} {ΓR = rCtx (factorExt e w) w'}
    (wkTm (factorWk e w ∙ factorWk (factorExt e w) w') t)
    (subst₂ (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')))
    ≅⟨ xcong
      (λ ΓL → Tm ΓL (◻ a)) (CExt Γ'')
      (sym (lCtxPres∙ e w w')) (sym (rCtxPres∙ e w w'))
      unbox
      factorWkPres∙-under-wkTm
      (≡-subst₂-removable (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w'))) ⟩
  unbox {ΓL = lCtx e (w ∙ w')} {ΓR = rCtx e (w ∙ w')} (wkTm (factorWk e (w ∙ w')) t) (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkTm (w ∙ w') (unbox t e) ∎
    where
      factorWkPres∙-under-wkTm :  wkTm (factorWk e w ∙ factorWk (factorExt e w) w') t ≅ wkTm (factorWk e (w ∙ w')) t
      factorWkPres∙-under-wkTm = HE.icong (ΓL ⊆_) (sym (lCtxPres∙ e w w')) (λ w → wkTm w t)
        (HE.trans (≡-to-≅ (sym (factorWkPres∙ e w w'))) (≡-subst-removable _ _ _))

wkSubPres∙ : (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') (s : Sub Δ Γ)
  → wkSub w' (wkSub w s) ≡ wkSub (w ∙ w') s
wkSubPres∙ w w' []         = refl
wkSubPres∙ w w' (s `, t)   = cong₂ _`,_ (wkSubPres∙ w w' s) (wkTmPres∙ w w' t)
wkSubPres∙ {Δ'' = Δ''} w w' (lock {ΔL = ΔL} {Γ = Γ} s e) = begin
  wkSub w' (wkSub w (lock s e))
    ≡⟨⟩
  lock (wkSub (factorWk (factorExt e w) w') (wkSub (factorWk e w) s)) (factorExt (factorExt e w) w')
    ≡⟨ cong₂ lock (wkSubPres∙ _ _ _ ) (sym (factorExtPres∙ _ _ _)) ⟩
  lock
    (wkSub (factorWk e w ∙ factorWk (factorExt e w) w') s)
    (subst₂ (CExt Δ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')))
    ≅⟨ xcong
      (λ ΔL → Sub ΔL Γ) (CExt Δ'')
      (sym (lCtxPres∙ e w w')) (sym (rCtxPres∙ e w w'))
      lock
      factorWkPres∙-under-wkSub
      (≡-subst₂-removable (CExt Δ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w'))) ⟩
  lock (wkSub (factorWk e (w ∙ w')) s) (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkSub (w ∙ w') (lock s e) ∎
    where
      factorWkPres∙-under-wkSub :  wkSub (factorWk e w ∙ factorWk (factorExt e w) w') s ≅ wkSub (factorWk e (w ∙ w')) s
      factorWkPres∙-under-wkSub = HE.icong (ΔL ⊆_) (sym (lCtxPres∙ e w w')) (λ w → wkSub w s)
        (HE.trans (≡-to-≅ (sym (factorWkPres∙ e w w'))) (≡-subst-removable _ _ _))

wkNePres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkNePres∙ w w' (app n m)   = cong₂ app (wkNePres∙ w w' n) (wkNfPres∙ w w' m)
wkNePres∙ {Γ'' = Γ''} w w' (unbox {ΓL = ΓL} {a = a} n e) = begin
  wkNe w' (wkNe w (unbox n e))
    ≡⟨⟩
  unbox
    (wkNe (factorWk (factorExt e w) w') (wkNe (factorWk e w) n))
    (factorExt (factorExt e w) w')
    ≡⟨ cong₂ unbox (wkNePres∙ _ _ n) (sym (factorExtPres∙ _ _ _)) ⟩
  unbox
    (wkNe (factorWk e w ∙ factorWk (factorExt e w) w') n)
    (subst₂ (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')))
    ≅⟨ xcong
      (λ ΓL → Ne ΓL (◻ a)) (CExt Γ'')
      (sym (lCtxPres∙ e w w')) (sym (rCtxPres∙ e w w'))
      unbox
      factorWkPres∙-under-wkNe
      (≡-subst₂-removable (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w'))) ⟩
  unbox {ΓL = lCtx e (w ∙ w')} {ΓR = rCtx e (w ∙ w')} (wkNe (factorWk e (w ∙ w')) n) (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkNe (w ∙ w') (unbox n e) ∎
    where
      factorWkPres∙-under-wkNe :  wkNe (factorWk e w ∙ factorWk (factorExt e w) w') n ≅ wkNe (factorWk e (w ∙ w')) n
      factorWkPres∙-under-wkNe = HE.icong (ΓL ⊆_) (sym (lCtxPres∙ e w w')) (λ w → wkNe w n)
        (HE.trans (≡-to-≅ (sym (factorWkPres∙ e w w'))) (≡-subst-removable _ _ _))

wkNfPres∙ w w' (up𝕓 n) = cong up𝕓 (wkNePres∙ w w' n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep w) (keep w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep🔒 w) (keep🔒 w') n)

private
  wkSubFreshLemma : {s : Sub Δ Γ} {w : Δ ⊆ Δ'}
    → wkSub (fresh {a = a}) (wkSub w s) ≡ wkSub (keep w) (dropₛ s)
  wkSubFreshLemma {s = s} {w} = trans (wkSubPres∙ w fresh s) (trans
    (cong₂ wkSub (cong drop (rightIdWk _)) refl )
    (sym (trans
      (wkSubPres∙ _ _ _)
      (cong₂ wkSub (cong drop (leftIdWk _)) refl))))

nat-substTm : (t : Tm Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substTm (wkSub w s) t ≡ wkTm w (substTm s t)
nat-substTm (var x)           s          w
  = nat-substVar x s w
nat-substTm (lam {Γ} {a} t)   s          w
  = cong lam
    (trans (cong (λ s → substTm (s `, var ze) t) wkSubFreshLemma)
    (nat-substTm t (keepₛ s) (keep w)))
nat-substTm (app t u)         s          w
  = cong₂ app (nat-substTm t s w) (nat-substTm u s w)
nat-substTm (box t)           s          w
  = cong box (nat-substTm t (lock s (ext🔒- nil)) (keep🔒 w))
nat-substTm {Γ = Γ} {Δ' = Δ'} (unbox {ΓL = ΓL} {a = a} t e) s w
  = begin
      substTm (wkSub w s) (unbox t e)
        ≡⟨⟩
      unbox {ΓL = lCtxₛ e (wkSub w s)} {ΓR = rCtxₛ e (wkSub w s)}
        (substTm (factorSubₛ e (wkSub w s)) t)
        (factorExtₛ e (wkSub w s))
        ≅⟨ xcong
          (λ ΓL →  Tm ΓL (◻ a)) (CExt Δ')
          (lCtxₛ-lCtx-comm e w s) (rCtxₛ-rCtx-comm e w s)
          unbox
          factorSubₛ-wkSub-comm-under-substTm
          (≡-subst₂-addable (CExt Δ') (lCtxₛ-lCtx-comm e w s) _ _) ⟩
     unbox {ΓL = lCtx (factorExtₛ e s) w} {ΓR = rCtx (factorExtₛ e s) w}
        (substTm (wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)) t)
        (subst₂ (CExt Δ') (lCtxₛ-lCtx-comm e w s) (rCtxₛ-rCtx-comm e w s) (factorExtₛ e (wkSub w s)))
        ≡⟨ cong₂ unbox (nat-substTm t _ _) (factorExtₛ-wkSub-comm e s _) ⟩
      unbox {ΓL = lCtx (factorExtₛ e s) w} {ΓR = rCtx (factorExtₛ e s) w}
        (wkTm (factorWk (factorExtₛ e s) w) (substTm (factorSubₛ e s) t))
        (factorExt (factorExtₛ e s) w)
        ≡⟨⟩
      wkTm w (substTm s (unbox t e)) ∎
      where
        factorSubₛ-wkSub-comm-under-substTm : substTm (factorSubₛ e (wkSub w s)) t ≅ substTm (wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)) t
        factorSubₛ-wkSub-comm-under-substTm = HE.icong (λ x → Sub x ΓL) (lCtxₛ-lCtx-comm e w s) (λ z → substTm z t)
          (HE.trans (≡-subst-addable _ _ _) (≡-to-≅ (factorSubₛ-wkSub-comm e s w)))

coh-wkSub-∙ₛ  : {Δ'' : Ctx} (s : Sub Δ Γ) (s' : Sub Δ' Δ) (w : Δ' ⊆ Δ'')
         → wkSub w (s ∙ₛ s') ≡ s ∙ₛ (wkSub w s')
coh-wkSub-∙ₛ []         s' w = refl
coh-wkSub-∙ₛ (s `, x)   s' w = cong₂ _`,_  (coh-wkSub-∙ₛ s s' w) (sym (nat-substTm x s' w))
coh-wkSub-∙ₛ (lock s e) s' w = begin
  wkSub w (lock s e ∙ₛ s')
    ≡⟨⟩
  lock
    (wkSub (factorWk (factorExtₛ e s') w) (s ∙ₛ factorSubₛ e s'))
    (factorExt (factorExtₛ e s') w)
    -- apply IH
    ≡⟨ cong₂ lock (coh-wkSub-∙ₛ _ _ _) refl ⟩
 lock
   (s ∙ₛ wkSub (factorWk (factorExtₛ e s') w) (factorSubₛ e s'))
   (factorExt (factorExtₛ e s') w)
   -- applying factoring equalities
   ≡⟨ cong₂ lock (cong (_ ∙ₛ_) (sym (factorSubₛ-wkSub-comm e s' w))) (sym (factorExtₛ-wkSub-comm e _ _)) ⟩
 lock
   (s ∙ₛ subst (λ ΔL → Sub ΔL _) (lCtxₛ-lCtx-comm e w s') (factorSubₛ e (wkSub w s')))
   (subst₂ (CExt _) (lCtxₛ-lCtx-comm e w s') (rCtxₛ-rCtx-comm e w s') (factorExtₛ e (wkSub w s')))
   -- remove substs
   ≅⟨ xcong
     (λ ΓL → Sub ΓL _) (CExt _)
     (sym (lCtxₛ-lCtx-comm e w s')) (sym (rCtxₛ-rCtx-comm e w s'))
     {t2 = s ∙ₛ factorSubₛ e (wkSub w s')}
     {e2 = factorExtₛ e (wkSub w s')}
     lock
     (HE.icong  (λ ΔL → Sub ΔL _) (sym (lCtxₛ-lCtx-comm e w s')) (s ∙ₛ_) (≡-subst-removable _ _ _))
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
  = cong lam (trans
    (cong (λ p → substTm (p `, var ze) t) (nat-trimSub s w fresh))
    (coh-trimSub-wkTm t (keepₛ s) (keep w)))
coh-trimSub-wkTm (app t u) s w
  = cong₂ app (coh-trimSub-wkTm t s w) (coh-trimSub-wkTm u s w)
coh-trimSub-wkTm (box t) s w
  = cong box (coh-trimSub-wkTm t (lock s (ext🔒- nil)) (keep🔒 w))
coh-trimSub-wkTm (unbox t e) s w
  = begin
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
           (HE.icong (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s w) (λ s' → substTm s' t) (≡-subst-addable _ _ _))
           (≡-subst₂-addable _ _ _ _) ⟩
    unbox
      (substTm (subst (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s w) (factorSubₛ e (trimSub w s))) t)
      (subst₂ (CExt _) (lCtxₛ-factorExt-trimSub-assoc e s w) (rCtxₛ-factorExt-trimSub-assoc e s w) (factorExtₛ e (trimSub w s)))
      -- apply factoring equalities
      ≡⟨ cong₂ unbox (cong₂ substTm {u = t} (factorSubₛ-trimSub-comm e s w) refl) (factorExtₛ-trimSub-comm e s w) ⟩
    unbox
      (substTm (trimSub (factorWk e w) (factorSubₛ (factorExt e w) s)) t)
      (factorExtₛ (factorExt e w) s)
      -- aplpy IH
      ≡⟨ cong₂ unbox (coh-trimSub-wkTm t _ _) refl ⟩
    unbox
      (substTm (factorSubₛ (factorExt e w) s) (wkTm (factorWk e w) t))
      (factorExtₛ (factorExt e w) s)
      ≡⟨⟩
    (substTm s (wkTm w (unbox t e))) ∎

coh-trimSub-wkSub  : {Δ₁ : Ctx} (s : Sub Δ Γ) (s' : Sub Δ₁ Δ') (w : Δ ⊆ Δ')
         → s ∙ₛ (trimSub w s') ≡ (wkSub w s) ∙ₛ s'
coh-trimSub-wkSub []         s' w
  = refl
coh-trimSub-wkSub (s `, x)   s' w
  = cong₂ _`,_ (coh-trimSub-wkSub s s' w) (coh-trimSub-wkTm x s' w)
coh-trimSub-wkSub (lock s e) s' w
  = begin
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
           (HE.icong  (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s' w) (s ∙ₛ_) (≡-subst-addable _ _ _))
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
      ≡⟨ cong₂ lock (coh-trimSub-wkSub _ _ _) refl ⟩
    lock
      (wkSub (factorWk e w) s ∙ₛ factorSubₛ (factorExt e w) s')
      (factorExtₛ (factorExt e w) s')
      ≡⟨⟩
    (wkSub w (lock s e) ∙ₛ s') ∎

lCtxₛPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → lCtxₛ e (factorSubₛ e' s) ≡ lCtxₛ (extRAssoc e e') s
lCtxₛPresTrans e nil        s          = refl
lCtxₛPresTrans e (ext e')   (s `, _)   = lCtxₛPresTrans e e' s
lCtxₛPresTrans e (ext🔒- e') (lock s _) = lCtxₛPresTrans e e' s

rCtxₛPresTrans : ∀ {ΓLL ΓLR : Ctx} (e : CExt ΓL ΓLL ΓLR) (e' : CExt Γ ΓL ΓR) (s : Sub Δ Γ)
  → rCtxₛ e (factorSubₛ e' s) ,, rCtxₛ e' s ≡ rCtxₛ (extRAssoc e e') s
rCtxₛPresTrans e nil        s                    = refl
rCtxₛPresTrans e (ext e')   (s `, t)             = rCtxₛPresTrans e e' s
rCtxₛPresTrans e (ext🔒- e') (lock {ΔR = ΔR} s _) = trans (sym (,,-assoc {ΓR = ΔR})) (cong (_,, ΔR) (rCtxₛPresTrans e e' s))

lCtxₛPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → lCtxₛ e (s ∙ₛ s') ≡ lCtxₛ (factorExtₛ e s) s'
lCtxₛPres∙ₛ nil       s s'           = refl
lCtxₛPres∙ₛ (ext e)   (s `, t) s'    = lCtxₛPres∙ₛ e s s'
lCtxₛPres∙ₛ (ext🔒- e) (lock s e1) s' = trans (lCtxₛPres∙ₛ e _ _) (lCtxₛPresTrans _ e1 _)

rCtxₛPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → rCtxₛ e (s ∙ₛ s') ≡ rCtxₛ (factorExtₛ e s) s'
rCtxₛPres∙ₛ nil       s s'           = refl
rCtxₛPres∙ₛ (ext e)   (s `, t) s'    = rCtxₛPres∙ₛ e s s'
rCtxₛPres∙ₛ (ext🔒- e) (lock s e1) s' = trans (cong (_,, _) (rCtxₛPres∙ₛ e _ _)) (rCtxₛPresTrans _ e1 _)

factorSubPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → subst (λ ΔL → Sub ΔL ΓL) (lCtxₛPres∙ₛ e s s') (factorSubₛ e (s ∙ₛ s'))  ≡ factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) s'
factorSubPres∙ₛ nil       s           s' = refl
factorSubPres∙ₛ (ext e)   (s `, t)    s' = factorSubPres∙ₛ e s s'
factorSubPres∙ₛ (ext🔒- e) (lock s e1) s' = TODO
  where
  postulate
    TODO : subst (λ ΔL → Sub ΔL _) (lCtxₛPres∙ₛ (ext🔒- e) (lock s e1) s') (factorSubₛ (ext🔒- e) (lock s e1 ∙ₛ s'))
           ≡
           factorSubₛ (ext🔒- e) (lock s e1) ∙ₛ factorSubₛ (factorExtₛ (ext🔒- e) (lock s e1)) s'

factorExtPres∙ₛ : (e : CExt Γ ΓL ΓR) (s : Sub Γ' Γ) (s' : Sub Δ Γ')
  → subst₂ (CExt _) (lCtxₛPres∙ₛ e s s') (rCtxₛPres∙ₛ e s s') (factorExtₛ e (s ∙ₛ s')) ≡ factorExtₛ (factorExtₛ e s) s'
factorExtPres∙ₛ _ _ _ = ExtIsProp _ _

substVarPresId : (x : Var Γ a) → substVar idₛ x ≡ var x
substVarPresId ze = refl
substVarPresId (su x) = trans (nat-substVar x idₛ fresh) (trans
  (cong (wkTm fresh) (substVarPresId x))
  (cong var (wkIncr x)))

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

substTmPres∙ : (s : Sub Γ' Γ) (s' : Sub Δ Γ') (t : Tm Γ a)
  → substTm s' (substTm s t) ≡ substTm (s ∙ₛ s') t
substTmPres∙ s s' (var v) = substVarPres∙ s s' v
substTmPres∙ s s' (lam t) = cong lam
    (trans (substTmPres∙ _ _ t)
    (cong ((λ s → substTm (s `, var ze) t)) (sym (dropKeepLemma s s'))))
substTmPres∙ s s' (app t t₁) = cong₂ app (substTmPres∙ s s' t) (substTmPres∙ s s' t₁)
substTmPres∙ s s' (box t) = cong box (substTmPres∙ _ _ t)
substTmPres∙ s s' (unbox t e) =
  trans
    (cong₂ unbox (substTmPres∙ (factorSubₛ e s) (factorSubₛ (factorExtₛ e s) s') t) refl)
    TODO
    where
    postulate
      TODO : unbox (substTm (factorSubₛ e s ∙ₛ factorSubₛ (factorExtₛ e s) s') t) (factorExtₛ (factorExtₛ e s) s') ≡ substTm (s ∙ₛ s') (unbox t e)

assocSub : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (s3 : Sub Γ3 Γ4) (s2 : Sub Γ2 Γ3) → (s1 : Sub Γ1 Γ2)
  → (s3 ∙ₛ s2) ∙ₛ s1 ≡ s3 ∙ₛ (s2 ∙ₛ s1)
assocSub []           s2 s1
  = refl
assocSub (s3 `, t)    s2 s1
  = cong₂ _`,_ (assocSub s3 s2 s1) (substTmPres∙ s2 s1 t)
assocSub (lock s3 e3) s2 s1
  = trans
    (cong₂ lock (assocSub s3 (factorSubₛ e3 s2) (factorSubₛ (factorExtₛ e3 s2) s1)) refl)
    TODO
    where
    postulate
      TODO :
        lock
          (s3 ∙ₛ factorSubₛ e3 s2 ∙ₛ factorSubₛ (factorExtₛ e3 s2) s1)
          (factorExtₛ (factorExtₛ e3 s2) s1)
        ≡ lock s3 e3 ∙ₛ s2 ∙ₛ s1

leftIdSub : (s : Sub Γ Γ') → (idₛ ∙ₛ s) ≡ s
leftIdSub []         = refl
leftIdSub (s `, t)   = cong₂ _`,_ (trans TODO (leftIdSub s)) refl
  where
  postulate
    TODO : dropₛ idₛ ∙ₛ (s `, t) ≡ idₛ ∙ₛ s

leftIdSub {Γ = Γ} (lock {ΔL = ΔL} {ΔR = ΔR} s e) = begin
  lock (idₛ ∙ₛ s) (extRAssoc nil e)
    ≡⟨ cong₂ lock (leftIdSub s) extLeftUnit ⟩
  lock s (subst (CExt Γ ΔL) _ e)
    ≅⟨ HE.icong (CExt Γ ΔL) ,,-leftUnit (lock s) (≡-subst-removable (CExt Γ ΔL) _ e) ⟩
  lock s e ∎

private
  -- just a helper to reduce redundancy, nothing too interesting
  auxLemma : (w : Γ ⊆ Δ) → wkSub (drop {a = a} (w ∙ idWk)) idₛ ≡ dropₛ (embWk w)

wkSubId : (w : Γ ⊆ Δ) → wkSub w idₛ ≡ embWk w

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
nat-embNe : (w : Γ ⊆ Γ') (n : Ne Γ a)
  → wkTm w (embNe n) ≡ embNe (wkNe w n)
nat-embNf : (w : Γ ⊆ Γ') (n : Nf Γ a)
  → wkTm w (embNf n) ≡ embNf (wkNf w n)

nat-embNf w (up𝕓 x) = nat-embNe w x
nat-embNf w (lam n) = cong lam (nat-embNf (keep w) n)
nat-embNf w (box n) = cong box (nat-embNf (keep🔒 w) n)

nat-embNe w (var x)     = refl
nat-embNe w (app n x)   = cong₂ app (nat-embNe w n) (nat-embNf w x)
nat-embNe w (unbox n x) = TODO
  where
  postulate
    TODO : wkTm w (embNe (unbox n x)) ≡ embNe (wkNe w (unbox n x))

-- Outcast lemmas

keepFreshLemma : {w : Γ ⊆ Γ'} {t : Tm Γ a}
  → wkTm (fresh {a = b}) (wkTm w t) ≡ wkTm (keep w) (wkTm fresh t)
keepFreshLemma = trans (wkTmPres∙ _ _ _) (sym (trans
    (wkTmPres∙ _ _ _)
    (cong₂ wkTm (cong drop (trans (leftIdWk _) (sym (rightIdWk _)))) refl)))

sliceCompLemma : (w : Γ ⊆ Δ) (e : LFExt Γ (ΓL 🔒) ΓR) (t : Tm (ΓL 🔒) a)
  → wkTm (LFExtTo≤ (wkLFExt e w)) (wkTm (keep🔒 (sliceLeft e w)) t) ≡      wkTm w (wkTm (LFExtTo≤ e) t)
sliceCompLemma w e t = (trans (wkTmPres∙ _ _ _) (sym (trans
  (wkTmPres∙ _ _ _)
  (cong₂ wkTm (slicingLemma w e) refl))))

beta-wk-lemma : (w  : Γ ⊆ Δ) (u : Tm Γ a) (t : Tm (Γ `, a) b)
  → substTm (idₛ `, wkTm w u) (wkTm (keep w) t) ≡ wkTm w (substTm (idₛ `, u) t)
beta-wk-lemma w u t = trans
  (sym (coh-trimSub-wkTm t _ (keep w)))
  (sym (trans
    (sym (nat-substTm t _ _))
    (cong
      (λ p → substTm (p `, wkTm w u) t)
      (sym (trans (trimSubId w) (sym (wkSubId w)))))))
