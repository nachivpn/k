{-# OPTIONS --safe --without-K #-}
module IK.Term.Base where

--
-- Implementation of the IK (Intuitionistic K) calculus from
-- "Fitch-Style Modal Lambda Calculi" by Ranald Clouston (2018)
--

open import Type                as Type using (Ty)
import Context.Base          Ty as Context
import Weakening.Base        Ty as Weakening
import ContextExtension.Base Ty as ContextExtension
import LocalVariable.Base    Ty as Variable
import Substitution             as Substitution

open Type             public
open Context          public
open Weakening        public
open ContextExtension public
open Variable         public

-------------------------------------
-- Variables, terms and substitutions
-------------------------------------

data Tm : Ctx → Ty → Set where

  var  : (v : Var Γ a)
       ---------------
       → Tm Γ a

  lam  : (t : Tm (Γ `, a) b)
         -------------------
       → Tm Γ (a ⇒ b)

  app  : (t : Tm Γ (a ⇒ b))
       → (u : Tm Γ a)
         ------------------
       → Tm Γ b

  box   : (t : Tm (Γ #) a)
        ------------------
        → Tm Γ (□ a)

  unbox : (t : Tm ΓL (□ a))
        → (e : LFExt Γ (ΓL #) ΓR)
        -------------------------
        → Tm Γ a

variable
  t t' t'' t''' : Tm Γ a
  u u' u'' u''' : Tm Γ a

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)                = var (wkVar w x)
wkTm w (lam t)                = lam (wkTm (keep w) t)
wkTm w (app t u)              = app (wkTm w t) (wkTm w u)
wkTm w (box t)                = box (wkTm (keep# w) t)
wkTm w (unbox t e)            = unbox (wkTm (sliceLeft e w) t) (wkLFExt e w)

leftWkTm : (t : Tm Γ a) → Tm (Δ ,, Γ) a
leftWkTm (var v)     = var (leftWkVar v)
leftWkTm (lam t)     = lam (leftWkTm t)
leftWkTm (app t u)   = app (leftWkTm t) (leftWkTm u)
leftWkTm (box t)     = box (leftWkTm t)
leftWkTm (unbox t e) = unbox (leftWkTm t) (leftWkLFExt e)

-- extension that "generates a new context frame"
pattern new      = nil
pattern new[_] Γ = nil {Γ}

open Substitution Ty Tm var wkTm (λ Γ ΓL ΓR → LFExt Γ (ΓL #) ΓR) new (λ {_Δ} {_Γ} {_ΓR} {Δ'} _e _w → ←# Δ') sliceLeft (λ {_Δ} {_Γ} {_ΓR} {Δ'} _e _w → #→ Δ') wkLFExt public
  renaming (module Composition to SubstitutionComposition)

-- "Left" context of factoring with a substitution (see factorSubₛ and factorExtₛ)
lCtxₛ : (e : LFExt Γ (ΓL #) ΓR) (s : Sub Δ Γ) → Ctx
lCtxₛ nil     (lock {ΔL = ΔL} s e) = ΔL
lCtxₛ (ext e) (s `, t)             = lCtxₛ e s

factorSubₛ : ∀ (e : LFExt Γ (ΓL #) ΓR) (s : Sub Δ Γ) → Sub (lCtxₛ e s) ΓL
factorSubₛ nil     (lock s e) = s
factorSubₛ (ext e) (s `, t)   = factorSubₛ e s

-- "Right" context of factoring with a substitution (see factorExtₛ)
rCtxₛ : (e : LFExt Γ (ΓL #) ΓR) (s : Sub Δ Γ) → Ctx
rCtxₛ nil     (lock {ΔR = ΔR} s e) = ΔR
rCtxₛ (ext e) (s `, t)             = rCtxₛ e s

factorExtₛ : ∀ (e : LFExt Γ (ΓL #) ΓR) (s : Sub Δ Γ) → LFExt Δ (lCtxₛ e s #) (rCtxₛ e s)
factorExtₛ nil     (lock s e) = e
factorExtₛ (ext e) (s `, _)   = factorExtₛ e s

-- apply substitution to a term
substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s (var x)     = substVar s x
substTm s (lam t)     = lam (substTm (keepₛ s) t)
substTm s (app t u)   = app (substTm s t) (substTm s u)
substTm s (box t)     = box (substTm (keep#ₛ s) t)
substTm s (unbox t e) = unbox (substTm (factorSubₛ e s) t) (factorExtₛ e s)

open SubstitutionComposition substTm lCtxₛ factorSubₛ rCtxₛ factorExtₛ public
