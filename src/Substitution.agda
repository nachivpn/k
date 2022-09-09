{-# OPTIONS --safe --without-K #-}

import Context.Base   as Context
import Weakening.Base as Weakening
import Variable.Base  as Variable

-------------------------------------------------------------------------------------
-- Substitutions (parameterized by terms `Tm` and modal accessibility relation `Acc`)
-------------------------------------------------------------------------------------

module Substitution
  (Ty          : Set)
  (let open Context   Ty using (Ctx ; _#))
  (let open Weakening Ty using (_⊆_))
  (let open Variable  Ty using (Var))
  (Tm          : (Γ : Ctx) → (a : Ty) → Set)
  (var         : {Γ : Ctx} → {a : Ty} → (v : Var Γ a) → Tm Γ a)
  (wkTm        : {Γ' Γ : Ctx} → {a : Ty} → (w : Γ ⊆ Γ') → (t : Tm Γ a) → Tm Γ' a)
  (Acc         : (Δ Γ ΓR : Ctx) → Set)
  {newR        : (Γ : Ctx) → Ctx}
  (new         : ∀ {Γ : Ctx} → Acc (Γ #) Γ (newR Γ))
  (lCtx        : {Δ Γ ΓR Δ' : Ctx} → (e : Acc Δ Γ ΓR) → (w : Δ ⊆ Δ') → Ctx)
  (factorWk    : ∀ {Δ Γ ΓR Δ' : Ctx} (e : Acc Δ Γ ΓR) (w : Δ ⊆ Δ') → Γ ⊆ lCtx e w)
  (rCtx        : {Δ Γ ΓR Δ' : Ctx} → (e : Acc Δ Γ ΓR) → (w : Δ ⊆ Δ') → Ctx)
  (factorExt   : ∀ {Δ Γ ΓR Δ' : Ctx} (e : Acc Δ Γ ΓR) (w : Δ ⊆ Δ') → Acc Δ' (lCtx e w) (rCtx e w))
  where

  -- "Cannot use generalized variable from let-opened module"
  open Context   Ty hiding (Ctx ; _#)
  open Weakening Ty hiding (_⊆_)
  open Variable  Ty hiding (Var)

  private
    variable
      a b c d : Ty

  data Sub : Ctx → Ctx → Set where
    []   : Sub Δ []
    _`,_ : (σ : Sub Δ  Γ) → (t : Tm Δ a)      → Sub Δ (Γ `, a)
    lock : (σ : Sub ΔL Γ) → (e : Acc Δ ΔL ΔR) → Sub Δ (Γ #)

  Sub- : Ctx → Ctx → Set
  Sub- Δ Γ = Sub Γ Δ

  variable
    s s' s'' : Sub Δ Γ
    σ σ' σ'' : Sub Δ Γ
    τ τ' τ'' : Sub Δ Γ

  -- composition operation for weakening after substitution
  trimSub : Δ ⊆ Γ → Sub Γ' Γ → Sub Γ' Δ
  trimSub base      []         = []
  trimSub (drop w)  (s `, x)   = trimSub w s
  trimSub (keep w)  (s `, x)   = (trimSub w s) `, x
  trimSub (keep# w) (lock s x) = lock (trimSub w s) x

  -- apply substitution to a variable
  substVar : Sub Γ Δ → Var Δ a → Tm Γ a
  substVar (s `, t)  zero     = t
  substVar (s `, _t) (succ v) = substVar s v

  -- weaken a substitution
  wkSub : Γ ⊆ Γ' → Sub Γ Δ → Sub Γ' Δ
  wkSub w []         = []
  wkSub w (s `, t)   = wkSub w s `, wkTm w t
  wkSub w (lock s e) = lock (wkSub (factorWk e w) s) (factorExt e w)

  -- NOTE: composition requires parallel substitution for terms

  -- "drop" the last variable in the context
  dropₛ : Sub Γ Δ → Sub (Γ `, a) Δ
  dropₛ s = wkSub fresh s

  -- "keep" the last variable in the context
  keepₛ : Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
  keepₛ s = dropₛ s `, var zero

  -- "keep" the lock in the context
  keep#ₛ : Sub Γ Δ → Sub (Γ #) (Δ #)
  keep#ₛ s = lock s new

  -- embed a weakening to substitution
  embWk : Δ ⊆ Γ → Sub Γ Δ
  embWk base      = []
  embWk (drop  w) = dropₛ  (embWk w)
  embWk (keep  w) = keepₛ  (embWk w)
  embWk (keep# w) = keep#ₛ (embWk w)

  -- identity substitution
  idₛ : Sub Γ Γ
  idₛ = embWk idWk

  idₛ[_] = λ Γ → idₛ {Γ}

  ExtToSub : Acc Γ ΓL ΓR → Sub Γ (ΓL #)
  ExtToSub e = lock idₛ e

  module Composition
    (substTm     : {Δ Γ : Ctx} → {a : Ty} → (σ : Sub Δ Γ) → (t : Tm Γ a) → Tm Δ a)
    (lCtxₛ       : {Δ Γ ΓR Θ : Ctx} → (e : Acc Δ Γ ΓR) → (σ : Sub Θ Δ) → Ctx)
    (factorSubₛ  : ∀ {Δ Γ ΓR Θ : Ctx} (e : Acc Δ Γ ΓR) (σ : Sub Θ Δ) → Sub (lCtxₛ e σ) Γ)
    (rCtxₛ       : {Δ Γ ΓR Θ : Ctx} → (e : Acc Δ Γ ΓR) → (σ : Sub Θ Δ) → Ctx)
    (factorExtₛ  : ∀ {Δ Γ ΓR Θ : Ctx} (e : Acc Δ Γ ΓR) (σ : Sub Θ Δ) → Acc Θ (lCtxₛ e σ) (rCtxₛ e σ))
    where

    infixr 20 _∙ₛ_

    -- substitution composition
    _∙ₛ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
    []        ∙ₛ s = []
    (s' `, t) ∙ₛ s = s' ∙ₛ s `, substTm s t
    lock s' e ∙ₛ s = lock (s' ∙ₛ factorSubₛ e s) (factorExtₛ e s)
