{-# OPTIONS --without-K #-}
module IK.Applications.Experiments where

import Context

open import IK.Norm.Base
open import IK.Term

open import IK.Applications.Neutrality

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- if `a` isn't a subformula (sf) of `Γ`,
-- then it isn't a sf of its prefix.
sfPrefix : ¬ (a ⊲ᶜ Γ) → Ext θ Γ ΓL ΓR → ¬ (a ⊲ᶜ ΓL)
sfPrefix noA nil        = noA
sfPrefix noA (ext e)    = sfPrefix (λ z → noA (there z)) e
sfPrefix noA (ext# x e) = sfPrefix (λ z → noA (there# z)) e

-- if 𝕓 is not a subformula of Γ, then any normal form
-- of the type `Nf Γ (𝕓 ⇒ 𝕓)` must be the identity function
uniqIdFun : ¬ (𝕓 ⊲ᶜ Γ) → (n : Nf Γ (𝕓 ⇒ 𝕓)) → n ≡ lam (up𝕓 (var zero))
uniqIdFun noB (lam (up𝕓 (var zero)))        = refl
uniqIdFun noB (lam (up𝕓 (var (succ x))))    = ⊥-elim (noB (neutrVar x))
uniqIdFun noB (lam (up𝕓 (app m n)))    with neutrality m
... | there p                               =
  ⊥-elim (noB (⊲-lift (sbr⇒ ⊲-refl) p))
uniqIdFun noB (lam (up𝕓 (unbox n (ext e)))) =
  ⊥-elim (sfPrefix noB e (⊲-lift (sb□ ⊲-refl) (there# (neutrality n))))

-- if there are no boxed-formulas in `Γ`, then there are no neutrals in `Γ #`
noLeftPeek : ({x : Ty} → ¬ (□ x ⊲ᶜ Γ)) → ¬ (Ne (Γ #) a)
noLeftPeek f (app n x)     = noLeftPeek f n
noLeftPeek f (unbox n nil) = f (neutrality n)

-- strengthening relation
data _⋗_  : Ctx → Ctx → Set where
  add#  : [] ⋗ [#]
  keep  : Γ ⋗ Δ → (Γ `, a) ⋗ (Δ `, a)
  keep# : Γ ⋗ Δ → (Γ #) ⋗ (Δ #)

-- strengthening is the identity on variables
strenVar : Γ' ⋗ Γ → Var Γ a → Var Γ' a
strenVar (keep w) zero     = zero
strenVar (keep w) (succ x) = succ (strenVar w x)

strenNe : Γ' ⋗ Γ → Ne Γ a → Ne Γ' a
strenNf : Γ' ⋗ Γ → Nf Γ a → Nf Γ' a

strenNe r          (var x)           = var (strenVar r x)
strenNe r          (app n x)         = app (strenNe r n) (strenNf r x)
strenNe add#       (unbox n nil)     = ⊥-elim (noClosedNe n)
strenNe (keep# r)  (unbox n nil)     = unbox (strenNe r n) nil
strenNe (keep r)   (unbox n (ext x)) = wkNe fresh (strenNe r (unbox n x))

strenNf r (up𝕓 x) = up𝕓 (strenNe r x)
strenNf r (lam n) = lam (strenNf (keep r) n)
strenNf r (box n) = box (strenNf (keep# r) n)

-- NOTE:
-- direct induction to show strengthing for terms fails;
-- consider a `t : Tm [] (□ a)` and defining
-- `strenTm : Γ' ⋗ Γ → Tm Γ a → Tm Γ' a`,
-- what should `strenTm add# (unbox t nil) : Tm [] a` be?

strenTm : Γ' ⋗ Γ → Tm Γ a → Tm Γ' a
strenTm r t = embNf (strenNf r (norm t))

module _ where

  -- Show that `a` is a theorem iff `□ a` is a theorem,
  -- i.e., [] ⊢ a iff [] ⊢ □ a.

  -- forth : Tm [] a → Tm Γ (□ a)
  -- forth t = {!!}

  back : Tm [] (□ a) → Tm [] a
  back t = embNf (strenNf add# (norm (unbox t nil)))

noFreeUnbox : ¬ (Nf [] (□ 𝕓 ⇒ 𝕓))
noFreeUnbox (lam (up𝕓 (var (succ ()))))
noFreeUnbox (lam (up𝕓 (app n _))) with neutrality n
... | here (sb□ ())
noFreeUnbox (lam (up𝕓 (unbox x (ext ()))))

noFreeBox : ¬ (Nf [] (𝕓 ⇒ □ 𝕓))
noFreeBox (lam (box (up𝕓 (app n _)))) with neutrality n
... | there# (here ())
... | there# (there ())
noFreeBox (lam (box (up𝕓 (unbox (var (succ ())) nil))))
noFreeBox (lam (box (up𝕓 (unbox (app n _) nil)))) with neutrality n
... | here ()
... | there ()
noFreeBox (lam (box (up𝕓 (unbox (unbox _ (ext ())) nil))))
