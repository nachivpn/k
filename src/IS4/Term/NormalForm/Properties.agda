{-# OPTIONS --safe --with-K #-}
module IS4.Term.NormalForm.Properties where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; subst₂ ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (refl to ≡-refl ; sym to ≡-sym)

open import HEUtil

open import IS4.Term.Base
open import IS4.Term.NormalForm.Base

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
nat-embNf w (box n) = cong box (nat-embNf (keep# w) n)

nat-embNe w (var x)     = ≡-refl
nat-embNe w (app n x)   = cong₂ app (nat-embNe w n) (nat-embNf w x)
nat-embNe w (unbox n e) = cong₂ unbox (nat-embNe (factorWk e w) n) ≡-refl

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var x)     = cong var (wkVarPresId x)
wkNePresId (app n m)   = cong₂ app (wkNePresId n) (wkNfPresId m)
wkNePresId {Γ = Γ} (unbox {ΓL = ΓL} {a = a} n e) = let open ≡-Reasoning in begin
  wkNe idWk (unbox n e)
    ≡⟨⟩
  unbox (wkNe (factorWk e idWk) n) (factorExt e idWk)
    ≅⟨ xcong
      (λ ΓL → Ne ΓL (□ a)) (CExt Γ)
      (lCtxPresId e) (rCtxPresId e)
      unbox
      factorWkPresId-under-wkNe
      (≡-subst₂-addable (CExt Γ) _ _ (factorExt _ _)) ⟩
  unbox (wkNe idWk n) (subst₂ (CExt Γ) (lCtxPresId e) (rCtxPresId e) (factorExt e idWk))
    ≡⟨ cong₂ unbox (wkNePresId n) (factorExtPresId e) ⟩
  unbox n e ∎
    where
      factorWkPresId-under-wkNe : wkNe (factorWk e idWk) n ≅ wkNe idWk n
      factorWkPresId-under-wkNe = ≅-cong (ΓL ⊆_) (lCtxPresId e) (λ w → wkNe w n)
        (≅-trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresId e)))

wkNfPresId (up𝕓 n) = cong up𝕓 (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

wkNePres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkNePres∙ w w' (app n m)   = cong₂ app (wkNePres∙ w w' n) (wkNfPres∙ w w' m)
wkNePres∙ {Γ'' = Γ''} w w' (unbox {ΓL = ΓL} {a = a} n e) = let open ≡-Reasoning in begin
  wkNe w' (wkNe w (unbox n e))
    ≡⟨⟩
  unbox
    (wkNe (factorWk (factorExt e w) w') (wkNe (factorWk e w) n))
    (factorExt (factorExt e w) w')
    ≡⟨ cong₂ unbox (wkNePres∙ _ _ n) (≡-sym (factorExtPres∙ _ _ _)) ⟩
  unbox
    (wkNe (factorWk e w ∙ factorWk (factorExt e w) w') n)
    (subst₂ (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')))
    ≅⟨ xcong
      (λ ΓL → Ne ΓL (□ a)) (CExt Γ'')
      (≡-sym (lCtxPres∙ e w w')) (≡-sym (rCtxPres∙ e w w'))
      unbox
      factorWkPres∙-under-wkNe
      (≡-subst₂-removable (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w'))) ⟩
  unbox {ΓL = lCtx e (w ∙ w')} {ΓR = rCtx e (w ∙ w')} (wkNe (factorWk e (w ∙ w')) n) (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkNe (w ∙ w') (unbox n e) ∎
    where
      factorWkPres∙-under-wkNe :  wkNe (factorWk e w ∙ factorWk (factorExt e w) w') n ≅ wkNe (factorWk e (w ∙ w')) n
      factorWkPres∙-under-wkNe = ≅-cong (ΓL ⊆_) (≡-sym (lCtxPres∙ e w w')) (λ w → wkNe w n)
        (≅-trans (≡-to-≅ (≡-sym (factorWkPres∙ e w w'))) (≡-subst-removable _ _ _))

wkNfPres∙ w w' (up𝕓 n) = cong up𝕓 (wkNePres∙ w w' n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep w) (keep w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep# w) (keep# w') n)
