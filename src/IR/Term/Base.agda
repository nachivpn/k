{-# OPTIONS --safe --without-K #-}
module IR.Term.Base where

open import Data.Product using (Σ ; _×_ ; _,_ ; -,_)

open import Type.Base              as Type
import Context.Base             Ty as Context
import IR.ContextExtension.Base Ty as ContextExtension
import IR.Variable.Base         Ty as Variable
import IR.Renaming.Base         Ty as Renaming

open Type             public
open Context          public
open ContextExtension public
open Variable         public
open Renaming         public

data Tm (Γ : Ctx) : (a : Ty) → Set where
  var : (v : Var Γ a) → Tm Γ a
  lam : (t : Tm (Γ `, a) b) → Tm Γ (a ⇒ b)
  app : (t : Tm Γ (a ⇒ b)) → (u : Tm Γ a) → Tm Γ b
  box : (t : Tm (Γ #) a) → Tm Γ (□ a)
  unb : (t : Tm Δ (□ a)) → (e : Ext Δ Γ) → Tm Γ a

variable
  t t' t'' : Tm Γ a
  u u' u'' : Tm Γ a

data Sub (Γ : Ctx) : (Δ : Ctx) → Set where
  []   : Sub Γ []
  _`,_ : (σ : Sub Γ Δ) → (t : Tm Γ a) → Sub Γ (Δ `, a)
  lock : (σ : Sub Θ Δ) → (e : Ext Θ Γ) → Sub Γ (Δ #) -- keep# σ ∘ e

variable
  σ σ' σ'' : Sub Δ Γ
  τ τ' τ'' : Sub Δ Γ

renTm : (r : Ren Δ Γ) → (v : Tm Γ a) → Tm Δ a
renTm r (var v)   = var (renVar r v)
renTm r (lam t)   = lam (renTm (keepRen r) t)
renTm r (app t u) = app (renTm r t) (renTm r u)
renTm r (box t)   = box (renTm (keepRen# r) t)
renTm r (unb t e) = unb (renTm (factorRen e r) t) (factorExt e r)

renSub : (r : Ren Δ Γ) → (σ : Sub Γ Θ) → Sub Δ Θ
renSub r []         = []
renSub r (σ `, t)   = renSub r σ `, renTm r t
renSub r (lock σ e) = lock (renSub (factorRen e r) σ) (factorExt e r)

Ren-to-Sub : (r : Ren Δ Γ) → Sub Δ Γ
Ren-to-Sub []         = []
Ren-to-Sub (r `, v)   = Ren-to-Sub r `, var v
Ren-to-Sub (lock r e) = lock (Ren-to-Sub r) e

module FactorSub where
  factor : (e : Ext Γ Δ) → (σ : Sub Θ Δ) → Σ Ctx λ Θ' → Sub Θ' Γ × Ext Θ' Θ
  factor new[ Γ ]     (lock σ e)  = -, σ , e                                                    -- id ∘ (keep# σ ∘ e)       = keep# σ  ∘ e
  factor (ext[ a ] e) (σ `, t)    = factor e σ                                                  -- (e ∘ drop) ∘ (σ `, t)    = e ∘ σ          = keep# σ' ∘ e'
  factor (ext#-    e) (lock σ e') = let (Γ' , σ' , e'') = factor e σ in Γ' , σ' , (e'' ∙Ext e') -- (e ∘ ε) ∘ (keep# σ ∘ e') = e ∘ σ ∘ ε ∘ e' = keep# σ' ∘ e'' ∘ ε ∘ e'

instance
  FactorSub : Factor Sub
  FactorSub = record { factor = FactorSub.factor }

open Factor FactorSub public using () renaming (factorS to factorSub)

dropSub[_] : (a : Ty) → (σ : Sub Δ Γ) → Sub (Δ `, a) Γ
-- dropSub[_] a []         = []
-- dropSub[_] a (σ `, t)   = dropSub[ a ] σ `, renTm freshRen[ a ] t
-- dropSub[_] a (lock σ e) = lock σ (ext[ a ] e) -- (keep# σ ∘ e) ∘ drop = keep# σ ∘ (e ∘ drop)
dropSub[_] a σ = renSub freshRen[ a ] σ
dropSub = λ {Δ} {Γ} {a} σ → dropSub[_] {Δ} {Γ} a σ

idSub[_] : (Γ : Ctx) → Sub Γ Γ
idSub[_] []       = []
idSub[_] (Γ `, a) = dropSub[ a ] idSub[ Γ ] `, var zero
idSub[_] (Γ #)    = lock idSub[ Γ ] new[ Γ ]
-- idSub[_] Γ = Ren-to-Sub idRen[ Γ ]
idSub = λ {Γ} → idSub[_] Γ

freshSub[_] : (a : Ty) → Sub (Γ `, a) Γ
freshSub[_] a = dropSub[ a ] idSub
freshSub = λ {Γ} {a} → freshSub[_] {Γ} a

keepSub[_] : (a : Ty) → (σ : Sub Δ Γ) → Sub (Δ `, a) (Γ `, a)
keepSub[_] a σ = dropSub[ a ] σ `, var zero
keepSub = λ {Δ} {Γ} {a} σ → keepSub[_] {Δ} {Γ} a σ

keepSub# : (σ : Sub Δ Γ) → Sub (Δ #) (Γ #)
keepSub# σ = lock σ new

-- R structure for terms and substitutions
dropSub# : (σ : Sub Δ Γ) → Sub (Δ #) Γ
dropSub# []         = []
dropSub# (σ `, t)   = dropSub# σ `, renTm εRen t
dropSub# (lock σ e) = lock σ (ext#- e)
-- dropSub# σ = renSub εRen σ

εSub[_] : (Γ : Ctx) → Sub (Γ #) Γ
εSub[_] Γ = dropSub# idSub[ Γ ]
εSub = λ {Γ} → εSub[ Γ ]

extTm : (e : Ext Γ Δ) → (t : Tm Γ a) → Tm Δ a
extTm e t = renTm (Ext-to-Ren e) t

Ext-to-Sub : (e : Ext Γ Δ) → Sub Δ Γ
Ext-to-Sub e = Ren-to-Sub (Ext-to-Ren e)

extSub : (e : Ext Γ Δ) → (σ : Sub Γ Θ) → Sub Δ Θ
extSub e []          = []
extSub e (σ `, t)    = extSub e σ `, extTm e t
extSub e (lock σ e') = lock σ (e' ∙Ext e)
-- extSub e σ = renSub (Ext-to-Ren e) σ
-- /R structure for terms

subVar : (σ : Sub Δ Γ) → (v : Var Γ a) → Tm Δ a
subVar (σ `, t)   zero      = t
subVar (σ `, t)   (succ  v) = subVar σ v
subVar (lock σ e) (succ# v) = subVar (extSub e σ) v

subTm : (σ : Sub Δ Γ) → (t : Tm Γ a) → Tm Δ a
subTm σ (var v)   = subVar σ v
subTm σ (lam t)   = lam (subTm (keepSub σ) t)
subTm σ (app t u) = app (subTm σ t) (subTm σ u)
subTm σ (box t)   = box (subTm (keepSub# σ) t)
subTm σ (unb t e) = unb (subTm (factorSub e σ) t) (factorExt e σ)

-- \.<C-g>Sub
_∙Sub_ : (σ : Sub Θ Δ) → (σ' : Sub Δ Γ) → Sub Θ Γ
σ ∙Sub []        = []
σ ∙Sub (σ' `, t) = σ ∙Sub σ' `, subTm σ t
σ ∙Sub lock σ' e = lock (factorSub e σ ∙Sub σ') (factorExt e σ)
