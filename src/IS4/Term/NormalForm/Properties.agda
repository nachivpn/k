{-# OPTIONS --safe --with-K #-}
module IS4.Term.NormalForm.Properties where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; subst₂ ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

open import PEUtil

open import IS4.Term.Base
open import IS4.Term.NormalForm.Base

private
  module _ {e : CExt Δ Γ ΓR} {e' : CExt Δ Γ' ΓR'} where
    cong-unbox≡′′ : {n : Ne Γ (□ a)} {n' : Ne Γ' (□ a)}
      → (Γ≡Γ' : Γ ≡ Γ')
      → (n≡n' : subst1 Ne Γ≡Γ' n ≡ n')
      → unbox n e ≡[ Ne Δ a ] unbox n' e'
    cong-unbox≡′′ Γ≡Γ' n≡n' =
      idcong₄ unbox Γ≡Γ' (extRUniq′ Γ≡Γ' e e') n≡n' (ExtIsProp _ _)

  cong-unbox≡ : {n : Ne Γ (□ a)} {n' : Ne Γ (□ a)}
    → (n≡n' : n ≡ n')
    → unbox n e ≡[ Ne _ a ] unbox n' e
  cong-unbox≡ = cong-unbox≡′′ ≡-refl

  cong-unbox≡2 : {n : Ne Γ (□ a)}
    → unbox n e ≡[ Ne _ a ] unbox n e'
  cong-unbox≡2 = cong-unbox≡′′ ≡-refl ≡-refl

  cong-unbox≡′ : {n : Ne Γ (□ a)} {n' : Ne Γ (□ a)}
    → (n≡n' : n ≡ n')
    → unbox n e ≡[ Ne _ a ] unbox n' e'
  cong-unbox≡′ = cong-unbox≡′′ ≡-refl

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

nat-embNf w (up  n) = nat-embNe w n
nat-embNf w (lam n) = cong lam (nat-embNf (keep w) n)
nat-embNf w (box n) = cong box (nat-embNf (keep# w) n)

nat-embNe w (var   v)   = ≡-refl
nat-embNe w (app   n m) = cong₂ app   (nat-embNe w n) (nat-embNf w m)
nat-embNe w (unbox n e) = cong1 unbox (nat-embNe (factorWk e w) n)

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var   v)   = cong  var (wkVarPresId v)
wkNePresId (app   n m) = cong₂ app (wkNePresId n) (wkNfPresId m)
wkNePresId (unbox n e) = let open ≡-Reasoning in begin
  wkNe idWk (unbox n e)
    ≡⟨⟩
  unbox (wkNe (factorWk e idWk) n) (factorExt e idWk)
    ≡⟨ cong-unbox≡′′
         (lCtxPresId e)
         (≡-trans
           (subst-application1′ wkNe (lCtxPresId e))
           (cong1 wkNe (factorWkPresId e)))
     ⟩
  unbox (wkNe idWk n) e
    ≡⟨ cong1 unbox (wkNePresId n) ⟩
  unbox n e ∎

wkNfPresId (up  n) = cong up  (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

wkNePres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙                 w w' (var        v)   = cong  var (wkVarPres∙ w w' v)
wkNePres∙                 w w' (app        n m) = cong₂ app (wkNePres∙  w w' n) (wkNfPres∙ w w' m)
wkNePres∙ {Γ'' = Γ''} {a} w w' (unbox {ΓL} n e) = let open ≡-Reasoning in begin
  wkNe w' (wkNe w (unbox n e))
    ≡⟨⟩
  unbox
    (wkNe (factorWk (factorExt e w) w') (wkNe (factorWk e w) n))
    (factorExt (factorExt e w) w')
    ≡⟨ cong-unbox≡′ (wkNePres∙ _ _ n) ⟩
  unbox
    (wkNe (factorWk e w ∙ factorWk (factorExt e w) w') n)
    (factorExt (factorExt e w) w')
    ≡˘⟨ cong-unbox≡′′
         (lCtxPres∙ e w w')
         (≡-trans
           (subst-application1′ wkNe (lCtxPres∙ e w w'))
           (cong1 wkNe (factorWkPres∙ e w w')))
      ⟩
  unbox (wkNe (factorWk e (w ∙ w')) n) (factorExt e (w ∙ w'))
    ≡⟨⟩
  wkNe (w ∙ w') (unbox n e) ∎

wkNfPres∙ w w' (up  n) = cong up  (wkNePres∙ w         w'         n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep  w) (keep  w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep# w) (keep# w') n)
