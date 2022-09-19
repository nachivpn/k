{-# OPTIONS --without-K --rewriting #-}
module IR.Renaming.Properties (Ty : Set) where

open import Agda.Builtin.Equality.Rewrite

open import Data.Product using () renaming (proj₁ to fst ; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open import PEUtil

open import Context.Base        Ty
open import IR.ContextExtension Ty
open import IR.Variable         Ty
open import IR.Renaming.Base    Ty

private
  variable
    a b c d : Ty

extRen-π₁ : (a : Ty) → (e : Ext Δ Θ) → (r : Ren Δ Γ) → extRen (ext[ a ] e) r ≡ dropRen[ a ] (extRen e r)
extRen-π₁ a e []                                  = refl
extRen-π₁ a e (r `, v)    rewrite extRen-π₁ a e r = refl
extRen-π₁ a e (lock r e')                         = refl

{-# REWRITE extRen-π₁ #-}

extRen-ε : (e : Ext Δ Θ) → (r : Ren Δ Γ) → extRen (ext#- e) r ≡ dropRen# (extRen e r)
extRen-ε e []                               = refl
extRen-ε e (r `, v)    rewrite extRen-ε e r = refl
extRen-ε e (lock r e')                      = refl

{-# REWRITE extRen-ε #-}

extRen-id : (r : Ren Δ Γ) → extRen new[ Δ ] r ≡ dropRen# r
extRen-id []                             = refl
extRen-id (r `, v)   rewrite extRen-id r = refl
extRen-id (lock r e)                     = refl

{-# REWRITE extRen-id #-}

extVar-∙ : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (v : Var Γ a) → extVar e' (extVar e v) ≡ extVar (e ∙Ext e') v
extVar-∙ e new[ Δ ]      v                         = refl
extVar-∙ e (ext[ a ] e') v rewrite extVar-∙ e e' v = refl
extVar-∙ e (ext#-    e') v rewrite extVar-∙ e e' v = refl

{-# REWRITE extVar-∙ #-}

extRen-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (r : Ren Γ Ξ) → extRen e' (extRen e r) ≡ extRen (e ∙Ext e') r
extRen-∙Ext e e' []                                       = refl
extRen-∙Ext e e' (r `, v)     rewrite extRen-∙Ext e e' r  = refl
extRen-∙Ext e e' (lock r e'') rewrite ∙Ext-assoc e'' e e' = refl

{-# REWRITE extRen-∙Ext #-}

renVar-π₁ : (b : Ty) → (r : Ren Δ Γ) → (v : Var Γ a) → renVar (dropRen[ b ] r) v ≡ succ (renVar r v)
renVar-π₁ b (r `, v)   zero      = refl
renVar-π₁ b (r `, v)   (succ  w) = renVar-π₁ b r w
renVar-π₁ b (lock r e) (succ# v) = renVar-π₁ b (extRen e r) v

{-# REWRITE renVar-π₁ #-}

renVar-ε : (r : Ren Δ Γ) → (v : Var Γ a) → renVar (dropRen# r) v ≡ succ# (renVar r v)
renVar-ε (r `, v)   zero      = refl
renVar-ε (r `, v)   (succ  w) = renVar-ε r w
renVar-ε (lock r e) (succ# v) = renVar-ε (extRen e r) v

{-# REWRITE renVar-ε #-}

pairRen-dropRen : (a : Ty) → (r : Ren Θ Δ) → (v : Var Θ a) → (r' : Ren Δ Γ) → (r `, v) ∙Ren dropRen[ a ] r' ≡ r ∙Ren r'
pairRen-dropRen a r v []                                           = refl
pairRen-dropRen a r v (r' `, w)   rewrite pairRen-dropRen a r v r' = refl
pairRen-dropRen a r v (lock r' e)                                  = refl

{-# REWRITE pairRen-dropRen #-}

factorCtx-dropRen : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorRen.factor e (dropRen[ a ] r) .fst ≡ factorCtx e r
factorCtx-dropRen new[ Γ ]     (lock r e)  = refl
factorCtx-dropRen (ext[ a ] e) (r `, v)    = factorCtx-dropRen e r
factorCtx-dropRen (ext#-    e) (lock r e') = refl

{-# REWRITE factorCtx-dropRen #-}

factorRen-dropRen : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorRen.factor e (dropRen[ a ] r) .snd .fst ≡ factorRen e r
factorRen-dropRen new[ Γ ]     (lock r e)  = refl
factorRen-dropRen (ext[ a ] e) (r `, v)    = factorRen-dropRen e r
factorRen-dropRen (ext#-    e) (lock r e') = refl

{-# REWRITE factorRen-dropRen #-}

factorExt-dropRen : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorRen.factor e (dropRen[ a ] r) .snd .snd ≡ ext[ a ] (factorExt e r)
factorExt-dropRen new[ Γ ]     (lock r e)  = refl
factorExt-dropRen (ext[ a ] e) (r `, v)    = factorExt-dropRen e r
factorExt-dropRen (ext#-    e) (lock r e') = refl

{-# REWRITE factorExt-dropRen #-}

factorCtx-dropRen# : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorRen.factor e (dropRen# r) .fst ≡ factorCtx e r
factorCtx-dropRen# new[ Γ ]     (lock r e)  = refl
factorCtx-dropRen# (ext[ a ] e) (r `, v)    = factorCtx-dropRen# e r
factorCtx-dropRen# (ext#-    e) (lock r e') = refl

{-# REWRITE factorCtx-dropRen# #-}

factorRen-dropRen# : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorRen.factor e (dropRen# r) .snd .fst ≡ factorRen e r
factorRen-dropRen# new[ Γ ]     (lock r e)  = refl
factorRen-dropRen# (ext[ a ] e) (r `, v)    = factorRen-dropRen# e r
factorRen-dropRen# (ext#-    e) (lock r e') = refl

{-# REWRITE factorRen-dropRen# #-}

factorExt-dropRen# : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorRen.factor e (dropRen# r) .snd .snd ≡ ext#- (factorExt e r)
factorExt-dropRen# new[ Γ ]     (lock r e)  = refl
factorExt-dropRen# (ext[ a ] e) (r `, v)    = factorExt-dropRen# e r
factorExt-dropRen# (ext#-    e) (lock r e') = refl

{-# REWRITE factorExt-dropRen# #-}

factorCtx-idRen : (e : Ext Γ Δ) → FactorRen.factor e idRen[ Δ ] .fst ≡ Γ
factorCtx-idRen new[ Γ ]     = refl
factorCtx-idRen (ext[ a ] e) = factorCtx-idRen e
factorCtx-idRen (ext#-    e) = factorCtx-idRen e

{-# REWRITE factorCtx-idRen #-}

factorRen-idRen : (e : Ext Γ Δ) → FactorRen.factor e idRen[ Δ ] .snd .fst ≡ idRen[ Γ ]
factorRen-idRen new[ Γ ]     = refl
factorRen-idRen (ext[ a ] e) = factorRen-idRen e
factorRen-idRen (ext#-    e) = factorRen-idRen e

{-# REWRITE factorRen-idRen #-}

factorExt-idRen : (e : Ext Γ Δ) → FactorRen.factor e idRen[ Δ ] .snd .snd ≡ e
factorExt-idRen new[ Γ ]     = refl
factorExt-idRen (ext[ a ] e) = cong ext[ a ] (factorExt-idRen e)
factorExt-idRen (ext#-    e) = cong ext#-    (factorExt-idRen e)

{-# REWRITE factorExt-idRen #-}

factorCtx-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (r : Ren Ξ Θ) → FactorRen.factor (e ∙Ext e') r .fst ≡ factorCtx e (factorRen e' r)
factorCtx-∙Ext e new[ Δ ]      (lock r e')  = refl
factorCtx-∙Ext e (ext[ a ] e') (r `, v)     = factorCtx-∙Ext e e' r
factorCtx-∙Ext e (ext#- e')    (lock r e'') = factorCtx-∙Ext e e' r

{-# REWRITE factorCtx-∙Ext #-}

factorRen-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (r : Ren Ξ Θ) → FactorRen.factor (e ∙Ext e') r .snd .fst ≡ factorRen e (factorRen e' r)
factorRen-∙Ext e new[ Δ ]      (lock r e')  = refl
factorRen-∙Ext e (ext[ a ] e') (r `, v)     = factorRen-∙Ext e e' r
factorRen-∙Ext e (ext#- e')    (lock r e'') = factorRen-∙Ext e e' r

{-# REWRITE factorRen-∙Ext #-}

factorExt-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (r : Ren Ξ Θ) → FactorRen.factor (e ∙Ext e') r .snd .snd ≡ factorExt e (factorRen e' r) ∙Ext factorExt e' r
factorExt-∙Ext e new[ Δ ]      (lock r e')  = refl
factorExt-∙Ext e (ext[ a ] e') (r `, v)     = factorExt-∙Ext e e' r
factorExt-∙Ext e (ext#- e')    (lock r e'') = trans (cong (_∙Ext e'') (factorExt-∙Ext e e' r)) (∙Ext-assoc (factorExt e (factorRen e' r)) (factorExt e' r) e'')

{-# REWRITE factorExt-∙Ext #-}

factorCtx-∙Ren : (e : Ext Γ Δ) → (r : Ren Ξ Θ) → (r' : Ren Θ Δ) → FactorRen.factor e (r ∙Ren r') .fst ≡ factorCtx (factorExt e r') r
factorCtx-∙Ren new[ Γ ]     r (lock r' e)  = refl
factorCtx-∙Ren (ext[ a ] e) r (r' `, v)    = factorCtx-∙Ren e r r'
factorCtx-∙Ren (ext#-    e) r (lock r' e') = factorCtx-∙Ren e (factorRen e' r) r'

{-# REWRITE factorCtx-∙Ren #-}

factorRen-∙Ren : (e : Ext Γ Δ) → (r : Ren Ξ Θ) → (r' : Ren Θ Δ) → FactorRen.factor e (r ∙Ren r') .snd .fst ≡ factorRen (factorExt e r') r ∙Ren factorRen e r'
factorRen-∙Ren new[ Γ ]     r (lock r' e)  = refl
factorRen-∙Ren (ext[ a ] e) r (r' `, v)    = factorRen-∙Ren e r r'
factorRen-∙Ren (ext#-    e) r (lock r' e') = factorRen-∙Ren e (factorRen e' r) r'

{-# REWRITE factorRen-∙Ren #-}

factorExt-∙Ren : (e : Ext Γ Δ) → (r : Ren Ξ Θ) → (r' : Ren Θ Δ) → FactorRen.factor e (r ∙Ren r') .snd .snd ≡ factorExt (factorExt e r') r
factorExt-∙Ren new[ Γ ]     r (lock r' e)  = refl
factorExt-∙Ren (ext[ a ] e) r (r' `, v)    = factorExt-∙Ren e r r'
factorExt-∙Ren (ext#-    e) r (lock r' e') = cong (_∙Ext factorExt e' r) (factorExt-∙Ren e (factorRen e' r) r')

{-# REWRITE factorExt-∙Ren #-}

factorCtx-Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → FactorRen.factor e (Ext-to-Ren e') .fst ≡ Γ
factorCtx-Ext e new[ Δ ]      = refl
factorCtx-Ext e (ext[ a ] e') = factorCtx-Ext e e'
factorCtx-Ext e (ext#-    e') = factorCtx-Ext e e'

{-# REWRITE factorCtx-Ext #-}

factorRen-Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → FactorRen.factor e (Ext-to-Ren e') .snd .fst ≡ idRen[ Γ ]
factorRen-Ext e new[ Δ ]      = refl
factorRen-Ext e (ext[ a ] e') = factorRen-Ext e e'
factorRen-Ext e (ext#-    e') = factorRen-Ext e e'

{-# REWRITE factorRen-Ext #-}

factorExt-Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → FactorRen.factor e (Ext-to-Ren e') .snd .snd ≡ e ∙Ext e'
factorExt-Ext e new[ Δ ]      = refl
factorExt-Ext e (ext[ a ] e') = cong ext[ a ] (factorExt-Ext e e')
factorExt-Ext e (ext#-    e') = cong ext#-    (factorExt-Ext e e')

{-# REWRITE factorExt-Ext #-}

renVar-id : (Γ : Ctx) → (v : Var Γ a) → renVar idRen[ Γ ] v ≡ v
renVar-id (Γ `, a) zero      = refl
renVar-id (Γ `, a) (succ  v) = cong succ  (renVar-id Γ v)
renVar-id (Γ #)    (succ# v) = cong succ# (renVar-id Γ v)

{-# REWRITE renVar-id #-}

idRen-unit-left : (r : Ren Δ Γ) → idRen[ Δ ] ∙Ren r ≡ r
idRen-unit-left []         = refl
idRen-unit-left (r `, v)   = cong   (_`, v) (idRen-unit-left r)
idRen-unit-left (lock r e) = cong1- lock    (idRen-unit-left r)

{-# REWRITE idRen-unit-left #-}

idRen-unit-right : (r : Ren Δ Γ) → r ∙Ren idRen[ Γ ] ≡ r
idRen-unit-right []         = refl
idRen-unit-right (r `, v)   = cong   (_`, v) (idRen-unit-right r)
idRen-unit-right (lock r e) = cong1- lock    (idRen-unit-right r)

{-# REWRITE idRen-unit-right #-}

renVar-extVar : (e : Ext Γ Δ) → (v : Var Γ a) → renVar (Ext-to-Ren e) v ≡ extVar e v
renVar-extVar new[ Γ ]     v = refl
renVar-extVar (ext[ a ] e) v = cong succ  (renVar-extVar e v)
renVar-extVar (ext#-    e) v = cong succ# (renVar-extVar e v)

renRen-extRen : (e : Ext Δ Θ) → (r : Ren Δ Γ) → Ext-to-Ren e ∙Ren r ≡ extRen e r
renRen-extRen e []          = refl
renRen-extRen e (r `, v)    = cong₂ _`,_ (renRen-extRen e r) (renVar-extVar e v)
renRen-extRen e (lock r e') = refl

factorCtx-extRen : (e : Ext Γ Δ) → (e' : Ext Θ Ξ) → (r : Ren Θ Δ) → FactorRen.factor e (extRen e' r) .fst ≡ factorCtx e r
factorCtx-extRen new[ Γ ]     e' (lock r e)   = refl
factorCtx-extRen (ext[ a ] e) e' (r `, v)     = factorCtx-extRen e e' r
factorCtx-extRen (ext#-    e) e' (lock r e'') = refl

{-# REWRITE factorCtx-extRen #-}

factorRen-extRen : (e : Ext Γ Δ) → (e' : Ext Θ Ξ) → (r : Ren Θ Δ) → FactorRen.factor e (extRen e' r) .snd .fst ≡ factorRen e r
factorRen-extRen new[ Γ ]     e' (lock r e)   = refl
factorRen-extRen (ext[ a ] e) e' (r `, v)     = factorRen-extRen e e' r
factorRen-extRen (ext#-    e) e' (lock r e'') = refl

{-# REWRITE factorRen-extRen #-}

factorExt-extRen : (e : Ext Γ Δ) → (e' : Ext Θ Ξ) → (r : Ren Θ Δ) → FactorRen.factor e (extRen e' r) .snd .snd ≡ factorExt e r ∙Ext e'
factorExt-extRen new[ Γ ]     e' (lock r e)   = refl
factorExt-extRen (ext[ a ] e) e' (r `, v)     = factorExt-extRen e e' r
factorExt-extRen (ext#-    e) e' (lock r e'') = sym (∙Ext-assoc (factorExt e r) e'' e')

{-# REWRITE factorExt-extRen #-}

dropRen-∙ : (a : Ty) → (r : Ren Θ Δ) → (r' : Ren Δ Γ) → dropRen[ a ] r ∙Ren r' ≡ dropRen[ a ] (r ∙Ren r')
dropRen-∙ a r []                                   = refl
dropRen-∙ a r (r' `, v)   rewrite dropRen-∙ a r r' = refl
dropRen-∙ a r (lock r' e)                          = refl

{-# REWRITE dropRen-∙ #-}

dropRen#-∙ : (r : Ren Θ Δ) → (r' : Ren Δ Γ) → dropRen# r ∙Ren r' ≡ dropRen# (r ∙Ren r')
dropRen#-∙ r []                                  = refl
dropRen#-∙ r (r' `, v)   rewrite dropRen#-∙ r r' = refl
dropRen#-∙ r (lock r' e)                         = refl

{-# REWRITE dropRen#-∙ #-}

keepRen-fun-id : keepRen[ a ] idRen[ Γ ] ≡ idRen[ Γ `, a ]
keepRen-fun-id = refl

keepRen-fun-∙ : keepRen[ a ] r ∙Ren keepRen[ a ] r' ≡ keepRen[ a ] (r ∙Ren r')
keepRen-fun-∙ = refl

keepRen#-fun-id : keepRen# idRen[ Γ ] ≡ idRen[ Γ # ]
keepRen#-fun-id = refl

keepRen#-fun-∙ : keepRen# r ∙Ren keepRen# r' ≡ keepRen# (r ∙Ren r')
keepRen#-fun-∙ = refl

Ext-to-Ren-∙ : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → Ext-to-Ren (e ∙Ext e') ≡ Ext-to-Ren e' ∙Ren Ext-to-Ren e
Ext-to-Ren-∙ e new[ Δ ]                                = refl
Ext-to-Ren-∙ e (ext[ a ] e') rewrite Ext-to-Ren-∙ e e' = refl
Ext-to-Ren-∙ e (ext#-    e') rewrite Ext-to-Ren-∙ e e' = refl

extVar-∙Ren : (e : Ext Δ Θ) → (r : Ren Δ Γ) → (v : Var Γ a) → extVar e (renVar r v) ≡ renVar (extRen e r) v
extVar-∙Ren e (r `, v)    zero                                            = refl
extVar-∙Ren e (r `, v)    (succ  w)                                       = extVar-∙Ren e r w
extVar-∙Ren e (lock r e') (succ# v) rewrite extVar-∙Ren e (extRen e' r) v = refl

lockRen-dropRen# : (r : Ren Θ' Δ) → (e : Ext Θ' Θ) → (r' : Ren Δ Γ) → lock r e ∙Ren dropRen# r' ≡ extRen e r ∙Ren r'
lockRen-dropRen# r e []                                           = refl
lockRen-dropRen# r e (r' `, v)    rewrite lockRen-dropRen# r e r' = refl
lockRen-dropRen# r e (lock r' e')                                 = refl

{-# REWRITE lockRen-dropRen# #-}

factor-comm : (e : Ext Γ Δ) → (r : Ren Θ Δ) → extRen (factorExt e r) (factorRen e r) ≡ r ∙Ren Ext-to-Ren e
factor-comm new[ Γ ]     (lock r e)  = refl
factor-comm (ext[ a ] e) (r `, v)    = factor-comm e r
factor-comm (ext#-    e) (lock r e') = factor-comm e (extRen e' r)

renVar-∙Ext : (r : Ren Θ Δ) → (e : Ext Γ Δ) → (v : Var Γ a) → renVar (r ∙Ren Ext-to-Ren e) v ≡ renVar r (extVar e v)
renVar-∙Ext (lock r e) new[ Δ ]      v = refl
renVar-∙Ext (r `, v₁)  (ext[ a ] e)  v = renVar-∙Ext r e v
renVar-∙Ext (lock r e) (ext#-    e') v = renVar-∙Ext (extRen e r) e' v

extRen-∙ : (e : Ext Θ Ξ) → (r : Ren Θ Δ) → (r' : Ren Δ Γ) → extRen e (r ∙Ren r') ≡ extRen e r ∙Ren r'
extRen-∙ e r []                                                       = refl
extRen-∙ e r (r' `, v)    rewrite extRen-∙ e r r' | extVar-∙Ren e r v = refl
extRen-∙ e r (lock r' e')                                             = refl

renVar-∙ : (r : Ren Θ Δ) → (r' : Ren Δ Γ) → (v : Var Γ a) → renVar (r ∙Ren r') v ≡ renVar r (renVar r' v)
renVar-∙ r (r' `, v)   zero      = refl
renVar-∙ r (r' `, v)   (succ  w) = renVar-∙ r r' w
renVar-∙ r (lock r' e) (succ# v) rewrite extRen-∙ (factorExt e r) (factorRen e r) r' | renVar-∙ (extRen (factorExt e r) (factorRen e r)) r' v | factor-comm e r | renVar-∙Ext r e (renVar r' v) | extVar-∙Ren e r' v = refl

{-# REWRITE renVar-∙ #-}

∙Ren-assoc : (r : Ren Ξ Θ) → (r' : Ren Θ Δ) → (r'' : Ren Δ Γ) → r ∙Ren (r' ∙Ren r'') ≡ (r ∙Ren r') ∙Ren r''
∙Ren-assoc r r' []                                                                                  = refl
∙Ren-assoc r r' (r'' `, v)   rewrite ∙Ren-assoc r r' r''                                            = refl
∙Ren-assoc r r' (lock r'' e) rewrite ∙Ren-assoc (factorRen (factorExt e r') r) (factorRen e r') r'' = refl
