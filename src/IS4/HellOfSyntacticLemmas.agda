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
