{-# OPTIONS --safe --with-K #-}
module IK.Term.NormalForm.Properties where

open import Relation.Binary.PropositionalEquality

open import IK.Term.Base

open import IK.Term.NormalForm.Base

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var x)     = cong var (wkVarPresId x)
wkNePresId (app n m)   = cong₂ app (wkNePresId n) (wkNfPresId m)
wkNePresId (unbox n e) with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
... | refl | refl = cong₂ unbox
  (trans (cong₂ wkNe (sliceLeftId e) refl) (wkNePresId n))
  (wkLFExtPresId e)

wkNfPresId (up𝕓 n) = cong up𝕓 (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

wkNePres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkNePres∙ w w' (app n m)   = cong₂ app (wkNePres∙ w w' n) (wkNfPres∙ w w' m)
wkNePres∙ w w' (unbox n e) = cong₂ unbox
  (trans (wkNePres∙ _ _ _) (cong₂ wkNe (sliceLeftPres∙ w' w e) refl)) (wkLFExtPres∙ w' w e)

wkNfPres∙ w w' (up𝕓 n) = cong up𝕓 (wkNePres∙ w w' n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep w) (keep w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep🔒 w) (keep🔒 w') n)

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
nat-embNe w (unbox n x) = cong₂ unbox (nat-embNe (sliceLeft x w) n) refl
