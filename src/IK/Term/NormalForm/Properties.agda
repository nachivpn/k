{-# OPTIONS --safe --without-K #-}
module IK.Term.NormalForm.Properties where

open import Data.Product using (-,_)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; cong₂)

open import IK.Term.Base

open import IK.Term.NormalForm.Base

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var   v)   = cong  var (wkVarPresId v)
wkNePresId (app   n m) = cong₂ app (wkNePresId  n) (wkNfPresId m)
wkNePresId (unbox n e) with ←#IsPre# e | #→IsPost# e
... | refl | refl = cong₂ unbox
  (trans (cong₂ wkNe (sliceLeftId e) refl) (wkNePresId n))
  (wkLFExtPresId e)

wkNfPresId (up  n) = cong up  (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

wkNePres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙ w w' (var   v)   = cong  var (wkVarPres∙ w w' v)
wkNePres∙ w w' (app   n m) = cong₂ app (wkNePres∙  w w' n) (wkNfPres∙ w w' m)
wkNePres∙ w w' (unbox n e) = cong₂ unbox
  (trans (wkNePres∙ _ _ _) (cong₂ wkNe (sliceLeftPres∙ w w' e) refl)) (wkLFExtPres∙ w w' e)

wkNfPres∙ w w' (up  n) = cong up  (wkNePres∙ w w' n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep w) (keep w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep# w) (keep# w') n)

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

nat-embNf w (up  x) = nat-embNe w x
nat-embNf w (lam n) = cong lam (nat-embNf (keep w) n)
nat-embNf w (box n) = cong box (nat-embNf (keep# w) n)

nat-embNe w (var x)     = refl
nat-embNe w (app n x)   = cong₂ app (nat-embNe w n) (nat-embNf w x)
nat-embNe w (unbox n x) = cong₂ unbox (nat-embNe (sliceLeft x w) n) refl

-------------
-- Neutrality
-------------

infix 5 _R_ _RCtx_

-- positive subformula that doesn't drop boxes
data _R_ : (a : Ty) → (b : Ty) → Set where
  ◻    :                   a R a
  ⇒◻   : (aRb : a R b) →   a R c ⇒ b
  □[◻] : (aRb : a R b) → □ a R □ b

-- positive subformula under as many boxes as locks
data _RCtx_ : (a : Ty) → (Γ : Ctx) → Set where
  here   : (aRb  :   a R    b)                   → a RCtx Γ `, b
  there  : (aRΓ  :   a RCtx Γ)                   → a RCtx Γ `, b
  there◁ : (□aRΔ : □ a RCtx Δ) → (Δ◁Γ : Δ ◁IK Γ) → a RCtx Γ

R-trans : (aRb : a R b) → (bRc : b R c) → a R c
R-trans aRb        ◻          = aRb
R-trans aRb        (⇒◻   bRc) = ⇒◻   (R-trans aRb bRc)
R-trans ◻          (□[◻] bRc) = □[◻] bRc
R-trans (□[◻] aRb) (□[◻] bRc) = □[◻] (R-trans aRb bRc)

R-cons : (aRb : a R b) → (bRΓ : b RCtx Γ) → a RCtx Γ
R-cons aRb (here   bRc)      = here   (R-trans aRb        bRc)
R-cons aRb (there  bRΓ)      = there  (R-cons  aRb        bRΓ)
R-cons aRb (there◁ □bRΔ Δ◁Γ) = there◁ (R-cons  (□[◻] aRb) □bRΔ) Δ◁Γ

neutrality-var : (v : Var Γ a) → a RCtx Γ
neutrality-var zero     = here  ◻
neutrality-var (succ v) = there (neutrality-var v)

neutrality : (n : Ne Γ a) → a RCtx Γ
neutrality (var   v)   = neutrality-var v
neutrality (app   n m) = R-cons (⇒◻ ◻) (neutrality n)
neutrality (unbox n e) = there◁ (neutrality n) (-, e)
