{-# OPTIONS --allow-unsolved-metas #-}
module IS4.Term.NormalForm.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import IS4.Term.Base
open import IS4.Term.Properties

open import IS4.Term.NormalForm.Base

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var x)     = cong var (wkVarPresId x)
wkNePresId (app n m)   = cong₂ app (wkNePresId n) (wkNfPresId m)
wkNePresId (unbox n e) = {!with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
... | refl | refl = cong₂ unbox
  (trans (cong₂ wkNe (sliceLeftId e) refl) (wkNePresId n))
  (wkLFExtPresId e)!}

wkNfPresId (up𝕓 n) = cong up𝕓 (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

wkNePres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkNePres∙ w w' (app n m)   = cong₂ app (wkNePres∙ w w' n) (wkNfPres∙ w w' m)
wkNePres∙ w w' (unbox n e) = {!cong₂ unbox
  (trans (wkNePres∙ _ _ _) (cong₂ wkNe (sliceLeftPres∙ w' w e) refl)) (wkLFExtPres∙ w' w e)!}

wkNfPres∙ w w' (up𝕓 n) = cong up𝕓 (wkNePres∙ w w' n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep w) (keep w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep🔒 w) (keep🔒 w') n)

embNe-natural : (w : Γ ⊆ Γ') (n : Ne Γ a) → wkTm w (embNe n) ≡ embNe (wkNe w n)
embNf-natural : (w : Γ ⊆ Γ') (n : Nf Γ a) → wkTm w (embNf n) ≡ embNf (wkNf w n)

embNf-natural w (up𝕓 x) = embNe-natural w x
embNf-natural w (lam n) = cong lam (embNf-natural (keep w) n)
embNf-natural w (box n) = cong box (embNf-natural (keep🔒 w) n)

embNe-natural w (var x)     = refl
embNe-natural w (app n x)   = cong₂ app (embNe-natural w n) (embNf-natural w x)
embNe-natural w (unbox n e) = cong₂ unbox (embNe-natural (factor2≤ e w) n) refl
