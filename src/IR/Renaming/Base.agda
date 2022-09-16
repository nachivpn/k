{-# OPTIONS --safe --without-K #-}
module IR.Renaming.Base (Ty : Set) where

open import Data.Product using (Σ ; _×_ ; _,_ ; -,_)

open import Context.Base             Ty
open import IR.ContextExtension.Base Ty
open import IR.Variable.Base         Ty

infixl 20 _∙Ren_

private
  variable
    a b c d : Ty

-- substitutions of variables only
data Ren (Γ : Ctx) : (Δ : Ctx) → Set where
  []   : Ren Γ []
  _`,_ : (r : Ren Γ Δ) → (v : Var Γ a) → Ren Γ (Δ `, a)
  lock : (r : Ren Θ Δ) → (e : Ext Θ Γ) → Ren Γ (Δ #)

variable
  r r' r'' : Ren Δ Γ

module FactorRen where
  factor : (e : Ext Γ Δ) → (r : Ren Θ Δ) → Σ Ctx λ Θ' → Ren Θ' Γ × Ext Θ' Θ
  factor new[ Γ ]     (lock r e)  = -, r , e                                                 -- id               ∘ (keep# r ∘ e) = keep# r ∘ e
  factor (ext[ a ] e) (r `, v)    = factor e r                                               -- (e ∘ fresh[ a ]) ∘ (r `, v)      = e ∘ r          = keep# r' ∘ e'
  factor (ext#-    e) (lock r e') = let (Γ' , r' , e'') = factor e r in _ , r' , e'' ∙Ext e' -- (e ∘ ε) ∘ (keep# r ∘ e')         = e ∘ r ∘ ε ∘ e' = keep# r' ∘ (e'' ∘ ε ∘ e')

instance
  FactorRen : Factor Ren
  FactorRen = record { factor = FactorRen.factor }

open Factor FactorRen public using () renaming (factorS to factorRen)

dropRen[_] : (a : Ty) → (r : Ren Δ Γ) → Ren (Δ `, a) Γ
dropRen[_] a []         = []
dropRen[_] a (r `, v)   = dropRen[ a ] r `, succ v
dropRen[_] a (lock r e) = lock r (ext[ a ] e)
dropRen = λ {Δ} {Γ} {a} r → dropRen[_] {Δ} {Γ} a r

keepRen[_] : (a : Ty) → (r : Ren Δ Γ) → Ren (Δ `, a) (Γ `, a)
keepRen[_] a r = dropRen[ a ] r `, zero
keepRen = λ {Δ} {Γ} {a} r → keepRen[_] {Δ} {Γ} a r

keepRen# : (r : Ren Δ Γ) → Ren (Δ #) (Γ #)
keepRen# r = lock r new

idRen[_] : (Γ : Ctx) → Ren Γ Γ
idRen[_] []       = []
idRen[_] (Γ `, a) = dropRen[ a ] idRen[ Γ ] `, zero
idRen[_] (Γ #)    = keepRen# idRen[ Γ ]
idRen = λ {Γ} → idRen[_] Γ

freshRen[_] : (a : Ty) → Ren (Γ `, a) Γ
freshRen[_] a = dropRen[ a ] idRen
freshRen = λ {Γ} {a} → freshRen[_] {Γ} a

-- R structure for renamings
dropRen# : (r : Ren Δ Γ) → Ren (Δ #) Γ
dropRen# []         = []
dropRen# (r `, v)   = dropRen# r `, succ# v
dropRen# (lock r e) = lock r (ext#- e) -- (keep# r ∘ e) ∘ ε = keep# r (e ∘ ε)

εRen[_] : (Γ : Ctx) → Ren (Γ #) Γ
εRen[_] Γ = dropRen# idRen[ Γ ]
εRen = λ {Γ} → εRen[_] Γ

Ext-to-Ren : (e : Ext Γ Δ) → Ren Δ Γ
Ext-to-Ren new[ Γ ]     = εRen[ Γ ]
Ext-to-Ren (ext[ a ] e) = dropRen[ a ] (Ext-to-Ren e)
Ext-to-Ren (ext#-    e) = dropRen#     (Ext-to-Ren e)

extRen : (e : Ext Δ Θ) → (r : Ren Δ Γ) → Ren Θ Γ -- r ∘ (ε ∘ e)
extRen e []          = []
extRen e (r `, v)    = extRen e r `, extVar e v
extRen e (lock r e') = lock r (e' ∙Ext e)
-- /R structure for renamings

renVar : (r : Ren Δ Γ) → (v : Var Γ a) → Var Δ a
renVar (r `, v)   zero      = v
renVar (r `, v)   (succ  w) = renVar r w
renVar (lock r e) (succ# v) = renVar (extRen e r) v

-- \.<C-g>Ren
_∙Ren_ : (r : Ren Θ Δ) → (r' : Ren Δ Γ) → Ren Θ Γ
r ∙Ren []          = []
r ∙Ren (r' `, v)   = r ∙Ren r' `, renVar r v
r ∙Ren (lock r' e) = lock (factorRen e r ∙Ren r') (factorExt e r)
