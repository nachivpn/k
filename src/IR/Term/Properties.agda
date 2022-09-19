{-# OPTIONS --without-K --rewriting #-}
module IR.Term.Properties where

open import Agda.Builtin.Equality.Rewrite

open import Data.Product using () renaming (proj₁ to fst ; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

open import PEUtil

open import IR.Term.Base

open import IR.ContextExtension.Properties Ty
open import IR.Renaming.Properties         Ty

renTm-fun-∙ : (r : Ren Θ Δ) → (r' : Ren Δ Γ) → (t : Tm Γ a) → renTm r (renTm r' t) ≡ renTm (r ∙Ren r') t
renTm-fun-∙ r r' (var v)   = refl
renTm-fun-∙ r r' (lam t)   rewrite renTm-fun-∙ (keepRen r) (keepRen r') t                        = refl
renTm-fun-∙ r r' (app t u) rewrite renTm-fun-∙ r r' t | renTm-fun-∙ r r' u                       = refl
renTm-fun-∙ r r' (box t)   rewrite renTm-fun-∙ (keepRen# r)                   (keepRen# r')    t = refl
renTm-fun-∙ r r' (unb t e) rewrite renTm-fun-∙ (factorRen (factorExt e r') r) (factorRen e r') t = refl

{-# REWRITE renTm-fun-∙ #-}

renSub-fun-∙ : (r : Ren Θ Δ) → (r' : Ren Δ Γ) → (σ : Sub Γ Ξ) → renSub r (renSub r' σ) ≡ renSub (r ∙Ren r') σ
renSub-fun-∙ r r' []                                                                                = refl
renSub-fun-∙ r r' (σ `, t)   rewrite renSub-fun-∙ r                              r'               σ = refl
renSub-fun-∙ r r' (lock σ e) rewrite renSub-fun-∙ (factorRen (factorExt e r') r) (factorRen e r') σ = refl

{-# REWRITE renSub-fun-∙ #-}

renTm-id : (t : Tm Γ a) → renTm idRen[ Γ ] t ≡ t
renTm-id (var v)                                   = refl
renTm-id (lam t)   rewrite renTm-id t              = refl
renTm-id (app t u) rewrite renTm-id t | renTm-id u = refl
renTm-id (box t)   rewrite renTm-id t              = refl
renTm-id (unb t e) rewrite renTm-id t              = refl

{-# REWRITE renTm-id #-}

renSub-id : (σ : Sub Γ Δ) → renSub idRen[ Γ ] σ ≡ σ
renSub-id []                             = refl
renSub-id (σ `, t)   rewrite renSub-id σ = refl
renSub-id (lock σ e) rewrite renSub-id σ = refl

{-# REWRITE renSub-id #-}

factorSubCtx-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (σ : Sub Ξ Θ) → FactorSub.factor (e ∙Ext e') σ .fst ≡ factorCtx e (factorSub e' σ)
factorSubCtx-∙Ext e new[ Δ ]      (lock σ e')  = refl
factorSubCtx-∙Ext e (ext[ a ] e') (σ `, v)     = factorSubCtx-∙Ext e e' σ
factorSubCtx-∙Ext e (ext#- e')    (lock σ e'') = factorSubCtx-∙Ext e e' σ

{-# REWRITE factorSubCtx-∙Ext #-}

factorSub-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (σ : Sub Ξ Θ) → FactorSub.factor (e ∙Ext e') σ .snd .fst ≡ factorSub e (factorSub e' σ)
factorSub-∙Ext e new[ Δ ]      (lock σ e')  = refl
factorSub-∙Ext e (ext[ a ] e') (σ `, v)     = factorSub-∙Ext e e' σ
factorSub-∙Ext e (ext#- e')    (lock σ e'') = factorSub-∙Ext e e' σ

{-# REWRITE factorSub-∙Ext #-}

factorSubExt-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (σ : Sub Ξ Θ) → FactorSub.factor (e ∙Ext e') σ .snd .snd ≡ factorExt e (factorSub e' σ) ∙Ext factorExt e' σ
factorSubExt-∙Ext e new[ Δ ]      (lock σ e')  = refl
factorSubExt-∙Ext e (ext[ a ] e') (σ `, v)     = factorSubExt-∙Ext e e' σ
factorSubExt-∙Ext e (ext#- e')    (lock σ e'') = trans (cong (_∙Ext e'') (factorSubExt-∙Ext e e' σ)) (∙Ext-assoc (factorExt e (factorSub e' σ)) (factorExt e' σ) e'')

{-# REWRITE factorSubExt-∙Ext #-}

factorCtx-∙Sub : (e : Ext Γ Δ) → (σ : Sub Ξ Θ) → (σ' : Sub Θ Δ) → FactorSub.factor e (σ ∙Sub σ') .fst ≡ factorCtx (factorExt e σ') σ
factorCtx-∙Sub new[ Γ ]     σ (lock σ' e)  = refl
factorCtx-∙Sub (ext[ a ] e) σ (σ' `, v)    = factorCtx-∙Sub e σ σ'
factorCtx-∙Sub (ext#-    e) σ (lock σ' e') = factorCtx-∙Sub e (factorSub e' σ) σ'

{-# REWRITE factorCtx-∙Sub #-}

factorSub-∙Sub : (e : Ext Γ Δ) → (σ : Sub Ξ Θ) → (σ' : Sub Θ Δ) → FactorSub.factor e (σ ∙Sub σ') .snd .fst ≡ factorSub (factorExt e σ') σ ∙Sub factorSub e σ'
factorSub-∙Sub new[ Γ ]     σ (lock σ' e)  = refl
factorSub-∙Sub (ext[ a ] e) σ (σ' `, v)    = factorSub-∙Sub e σ σ'
factorSub-∙Sub (ext#-    e) σ (lock σ' e') = factorSub-∙Sub e (factorSub e' σ) σ'

{-# REWRITE factorSub-∙Sub #-}

factorExt-∙Sub : (e : Ext Γ Δ) → (σ : Sub Ξ Θ) → (σ' : Sub Θ Δ) → FactorSub.factor e (σ ∙Sub σ') .snd .snd ≡ factorExt (factorExt e σ') σ
factorExt-∙Sub new[ Γ ]     σ (lock σ' e)  = refl
factorExt-∙Sub (ext[ a ] e) σ (σ' `, v)    = factorExt-∙Sub e σ σ'
factorExt-∙Sub (ext#-    e) σ (lock σ' e') = cong (_∙Ext factorExt e' σ) (factorExt-∙Sub e (factorSub e' σ) σ')

{-# REWRITE factorExt-∙Sub #-}

factorCtx-extSub : (e : Ext Γ Δ) → (e' : Ext Θ Ξ) → (σ : Sub Θ Δ) → FactorSub.factor e (extSub e' σ) .fst ≡ factorCtx e σ
factorCtx-extSub new[ Γ ]     e' (lock σ e)   = refl
factorCtx-extSub (ext[ a ] e) e' (σ `, v)     = factorCtx-extSub e e' σ
factorCtx-extSub (ext#-    e) e' (lock σ e'') = refl

{-# REWRITE factorCtx-extSub #-}

factorSub-extSub : (e : Ext Γ Δ) → (e' : Ext Θ Ξ) → (σ : Sub Θ Δ) → FactorSub.factor e (extSub e' σ) .snd .fst ≡ factorSub e σ
factorSub-extSub new[ Γ ]     e' (lock σ e)   = refl
factorSub-extSub (ext[ a ] e) e' (σ `, v)     = factorSub-extSub e e' σ
factorSub-extSub (ext#-    e) e' (lock σ e'') = refl

{-# REWRITE factorSub-extSub #-}

factorExt-extSub : (e : Ext Γ Δ) → (e' : Ext Θ Ξ) → (σ : Sub Θ Δ) → FactorSub.factor e (extSub e' σ) .snd .snd ≡ factorExt e σ ∙Ext e'
factorExt-extSub new[ Γ ]     e' (lock σ e)   = refl
factorExt-extSub (ext[ a ] e) e' (σ `, v)     = factorExt-extSub e e' σ
factorExt-extSub (ext#-    e) e' (lock σ e'') = sym (∙Ext-assoc (factorExt e σ) e'' e')

{-# REWRITE factorExt-extSub #-}

factorCtx-renSub : (e : Ext Γ Δ) → (r : Ren Ξ Θ) → (σ : Sub Θ Δ) → FactorSub.factor e (renSub r σ) .fst ≡ factorCtx (factorExt e σ) r
factorCtx-renSub new[ Γ ]     r (lock σ e)  = refl
factorCtx-renSub (ext[ a ] e) r (σ `, v)    = factorCtx-renSub e r σ
factorCtx-renSub (ext#-    e) r (lock σ e') = factorCtx-renSub e (factorRen e' r) σ

{-# REWRITE factorCtx-renSub #-}

factorSub-renSub : (e : Ext Γ Δ) → (r : Ren Ξ Θ) → (σ : Sub Θ Δ) → FactorSub.factor e (renSub r σ) .snd .fst ≡ renSub (factorRen (factorExt e σ) r) (factorSub e σ)
factorSub-renSub new[ Γ ]     r (lock σ e)  = refl
factorSub-renSub (ext[ a ] e) r (σ `, v)    = factorSub-renSub e r σ
factorSub-renSub (ext#-    e) r (lock σ e') = factorSub-renSub e (factorRen e' r) σ

{-# REWRITE factorSub-renSub #-}

factorExt-renSub : (e : Ext Γ Δ) → (r : Ren Ξ Θ) → (σ : Sub Θ Δ) → FactorSub.factor e (renSub r σ) .snd .snd ≡ factorExt (factorExt e σ) r
factorExt-renSub new[ Γ ]     r (lock σ e)  = refl
factorExt-renSub (ext[ a ] e) r (σ `, v)    = factorExt-renSub e r σ
factorExt-renSub (ext#-    e) r (lock σ e') = cong (_∙Ext factorExt e' r) (factorExt-renSub e (factorRen e' r) σ)

{-# REWRITE factorExt-renSub #-}

factorCtx-idSub : (e : Ext Γ Δ) → FactorSub.factor e idSub[ Δ ] .fst ≡ Γ
factorCtx-idSub new[ Γ ]     = refl
factorCtx-idSub (ext[ a ] e) = factorCtx-idSub e
factorCtx-idSub (ext#-    e) = factorCtx-idSub e

{-# REWRITE factorCtx-idSub #-}

factorSub-idSub : (e : Ext Γ Δ) → FactorSub.factor e idSub[ Δ ] .snd .fst ≡ idSub[ Γ ]
factorSub-idSub new[ Γ ]     = refl
factorSub-idSub (ext[ a ] e) = factorSub-idSub e
factorSub-idSub (ext#-    e) = factorSub-idSub e

{-# REWRITE factorSub-idSub #-}

factorExt-idSub : (e : Ext Γ Δ) → FactorSub.factor e idSub[ Δ ] .snd .snd ≡ e
factorExt-idSub new[ Γ ]     = refl
factorExt-idSub (ext[ a ] e) = cong ext[ a ] (factorExt-idSub e)
factorExt-idSub (ext#-    e) = cong ext#-    (factorExt-idSub e)

{-# REWRITE factorExt-idSub #-}

factorCtx-factorRenCtx : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorSub.factor e (Ren-to-Sub r) .fst ≡ factorCtx e r
factorCtx-factorRenCtx new[ Γ ]     (lock r e)  = refl
factorCtx-factorRenCtx (ext[ a ] e) (r `, v)    = factorCtx-factorRenCtx e r
factorCtx-factorRenCtx (ext#-    e) (lock r e') = factorCtx-factorRenCtx e r

{-# REWRITE factorCtx-factorRenCtx #-}

factorSub-factorRen : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorSub.factor e (Ren-to-Sub r) .snd .fst ≡ Ren-to-Sub (factorRen e r)
factorSub-factorRen new[ Γ ]     (lock r e)  = refl
factorSub-factorRen (ext[ a ] e) (r `, v)    = factorSub-factorRen e r
factorSub-factorRen (ext#-    e) (lock r e') = factorSub-factorRen e r

{-# REWRITE factorSub-factorRen #-}

factorExt-factorRenExt : (e : Ext Γ Δ) → (r : Ren Θ Δ) → FactorSub.factor e (Ren-to-Sub r) .snd .snd ≡ factorExt e r
factorExt-factorRenExt new[ Γ ]     (lock r e)                                     = refl
factorExt-factorRenExt (ext[ a ] e) (r `, v)                                       = factorExt-factorRenExt e r
factorExt-factorRenExt (ext#-    e) (lock r e') rewrite factorExt-factorRenExt e r = refl

{-# REWRITE factorExt-factorRenExt #-}

dropSub-dropRen : (a : Ty) → (r : Ren Δ Γ) → dropSub[ a ] (Ren-to-Sub r) ≡ Ren-to-Sub (dropRen[ a ] r)
dropSub-dropRen a []                                     = refl
dropSub-dropRen a (r `, v)   rewrite dropSub-dropRen a r = refl
dropSub-dropRen a (lock r e)                             = refl

keepSub-keepRen : (a : Ty) → (r : Ren Δ Γ) → keepSub[ a ] (Ren-to-Sub r) ≡ Ren-to-Sub (keepRen[ a ] r)
keepSub-keepRen a r rewrite dropSub-dropRen a r = refl

renSub-Ren : (r : Ren Θ Δ) → (r' : Ren Δ Γ) → renSub r (Ren-to-Sub r') ≡ Ren-to-Sub (r ∙Ren r')
renSub-Ren r []                                                = refl
renSub-Ren r (r' `, v)   rewrite renSub-Ren r               r' = refl
renSub-Ren r (lock r' e) rewrite renSub-Ren (factorRen e r) r' = refl

{-# REWRITE renSub-Ren #-}

idSub-idRen : (Γ : Ctx) → idSub[ Γ ] ≡ Ren-to-Sub (idRen[ Γ ])
idSub-idRen []                             = refl
idSub-idRen (Γ `, a) rewrite idSub-idRen Γ = refl
idSub-idRen (Γ #)    rewrite idSub-idRen Γ = refl

pairSub-dropRen : (σ : Sub Θ Δ) → (t : Tm Θ a) → (r : Ren Δ Γ) → (σ `, t) ∙Sub Ren-to-Sub (dropRen[ a ] r) ≡ σ ∙Sub Ren-to-Sub r
pairSub-dropRen σ t []                                       = refl
pairSub-dropRen σ t (r `, v)   rewrite pairSub-dropRen σ t r = refl
pairSub-dropRen σ t (lock r e)                               = refl

{-# REWRITE pairSub-dropRen #-}

idRen-unit-right-∙Sub : (Γ : Ctx) → (σ : Sub Δ Γ) → σ ∙Sub Ren-to-Sub idRen[ Γ ] ≡ σ
idRen-unit-right-∙Sub []       []                                           = refl
idRen-unit-right-∙Sub (Γ `, a) (σ `, t)   rewrite idRen-unit-right-∙Sub Γ σ = refl
idRen-unit-right-∙Sub (Γ #)    (lock σ e) rewrite idRen-unit-right-∙Sub Γ σ = refl

{-# REWRITE idRen-unit-right-∙Sub #-}

lockSub-dropRen# : (σ : Sub Θ' Δ) → (e : Ext Θ' Θ) → (r : Ren Δ Γ) → lock σ e ∙Sub Ren-to-Sub (dropRen# r) ≡ extSub e σ ∙Sub Ren-to-Sub r
lockSub-dropRen# σ e []                                           = refl
lockSub-dropRen# σ e (σ' `, t)    rewrite lockSub-dropRen# σ e σ' = refl
lockSub-dropRen# σ e (lock σ' e')                                 = refl

{-# REWRITE lockSub-dropRen# #-}

extSub-extRen : (e : Ext Δ Θ) → (r : Ren Δ Γ) → extSub e (Ren-to-Sub r) ≡ Ren-to-Sub (extRen e r)
extSub-extRen e []                                                        = refl
extSub-extRen e (r `, v)    rewrite extSub-extRen e r | renVar-extVar e v = refl
extSub-extRen e (lock r e')                                               = refl

subVar-renVar : (r : Ren Δ Γ) → (v : Var Γ a) → subVar (Ren-to-Sub r) v ≡ var (renVar r v)
subVar-renVar (r `, v)   zero                                                               = refl
subVar-renVar (r `, v)   (succ  w)                                                          = subVar-renVar r w
subVar-renVar (lock r e) (succ# v) rewrite extSub-extRen e r | subVar-renVar (extRen e r) v = refl

{-# REWRITE subVar-renVar #-}

subTm-renTm : (r : Ren Δ Γ) → (t : Tm Γ a) → subTm (Ren-to-Sub r) t ≡ renTm r t
subTm-renTm r (var v)                                               = refl
subTm-renTm r (lam {a} t) rewrite subTm-renTm (keepRen r) t         = refl
subTm-renTm r (app t u)   rewrite subTm-renTm r t | subTm-renTm r u = refl
subTm-renTm r (box t)     rewrite subTm-renTm (keepRen# r)    t     = refl
subTm-renTm r (unb t e)   rewrite subTm-renTm (factorRen e r) t     = refl

{-# REWRITE subTm-renTm #-}

renSub-extSub : (e : Ext Δ Θ) → (σ : Sub Δ Γ) → extSub e σ ≡ renSub (Ext-to-Ren e) σ
renSub-extSub e []                                    = refl
renSub-extSub e (σ `, t)    rewrite renSub-extSub e σ = refl
renSub-extSub e (lock σ e')                           = refl

extSub-renSub : (e : Ext Θ Ξ) → (r : Ren Θ Δ) → (σ : Sub Δ Γ) → extSub e (renSub r σ) ≡ renSub (extRen e r) σ
extSub-renSub e r []                                                          = refl
extSub-renSub e r (σ `, t)    rewrite extSub-renSub e r σ | renRen-extRen e r = refl
extSub-renSub e r (lock σ e')                                                 = refl

renTm-subVar : (r : Ren Θ Δ) → (σ : Sub Δ Γ) → (v : Var Γ a) → renTm r (subVar σ v) ≡ subVar (renSub r σ) v
renTm-subVar r (σ `, t)   zero                                                                                                                                      = refl
renTm-subVar r (σ `, t)   (succ  v)                                                                                                                                 = renTm-subVar r σ v
renTm-subVar r (lock σ e) (succ# v) rewrite renTm-subVar r (extSub e σ) v | renSub-extSub e σ | extSub-renSub (factorExt e r) (factorRen e r) σ | factor-comm e r = refl

renTm-subTm : (r : Ren Θ Δ) → (σ : Sub Δ Γ) → (t : Tm Γ a) → renTm r (subTm σ t) ≡ subTm (renSub r σ) t
renTm-subTm r σ (var v)                                                                       = renTm-subVar r σ v
renTm-subTm r σ (lam t)   rewrite renTm-subTm (keepRen r) (keepSub σ) t                       = refl
renTm-subTm r σ (app t u) rewrite renTm-subTm r σ t | renTm-subTm r σ u                       = refl
renTm-subTm r σ (box t)   rewrite renTm-subTm (keepRen# r)                  (keepSub# σ)    t = refl
renTm-subTm r σ (unb t e) rewrite renTm-subTm (factorRen (factorExt e σ) r) (factorSub e σ) t = refl

renSub-subSub : (r : Ren Θ Δ) → (σ : Sub Δ Γ) → (τ : Sub Γ Ξ) → renSub r (σ ∙Sub τ) ≡ renSub r σ ∙Sub τ
renSub-subSub r σ []                                                                               = refl
renSub-subSub r σ (τ `, t)   rewrite renSub-subSub r σ τ | renTm-subTm r σ t                       = refl
renSub-subSub r σ (lock τ e) rewrite renSub-subSub (factorRen (factorExt e σ) r) (factorSub e σ) τ = refl

extSub-∙ : (e : Ext Θ Ξ) → (r : Sub Θ Δ) → (r' : Sub Δ Γ) → extSub e (r ∙Sub r') ≡ extSub e r ∙Sub r'
extSub-∙ e r []                                                                                        = refl
extSub-∙ e r (r' `, v)    rewrite extSub-∙ e r r' | renTm-subTm (Ext-to-Ren e) r v | renSub-extSub e r = refl
extSub-∙ e r (lock r' e')                                                                              = refl

extSub-∙Ext : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (σ : Sub Γ Ξ) → extSub e' (extSub e σ) ≡ extSub (e ∙Ext e') σ
extSub-∙Ext e e' []                                                          = refl
extSub-∙Ext e e' (σ `, v)     rewrite extSub-∙Ext e e' σ | Ext-to-Ren-∙ e e' = refl
extSub-∙Ext e e' (lock σ e'') rewrite ∙Ext-assoc e'' e e'                    = refl

subVar-∙Ext : (σ : Sub Θ Δ) → (e : Ext Γ Δ) → (v : Var Γ a) → subVar (σ ∙Sub Ext-to-Sub e) v ≡ subVar σ (extVar e v)
subVar-∙Ext (lock σ e) new[ Δ ]     v                                       = refl
subVar-∙Ext (σ `, t)   (ext[ a ] e) v                                       = subVar-∙Ext σ e v
subVar-∙Ext (lock σ e) (ext#- e')   v rewrite subVar-∙Ext (extSub e σ) e' v = refl

factorSub-comm : (e : Ext Γ Δ) → (σ : Sub Θ Δ) → extSub (factorExt e σ) (factorSub e σ) ≡ σ ∙Sub Ext-to-Sub e
factorSub-comm new[ Γ ]     (lock σ e)  = refl
factorSub-comm (ext[ a ] e) (σ `, t)    = factorSub-comm e σ
factorSub-comm (ext#- e)    (lock σ e') = factorSub-comm e (extSub e' σ)

subVar-∙Ren : (σ : Sub Θ Δ) → (r : Ren Δ Γ) → (v : Var Γ a) → subVar σ (renVar r v) ≡ subVar (σ ∙Sub Ren-to-Sub r) v
subVar-∙Ren σ (r `, v)   zero      = refl
subVar-∙Ren σ (r `, v)   (succ  w) = subVar-∙Ren σ r w
subVar-∙Ren σ (lock r e) (succ# v) rewrite extSub-∙ (factorExt e σ) (factorSub e σ) (Ren-to-Sub r) | factorSub-comm e σ | sym (extVar-∙Ren e r v) | sym (subVar-∙Ext σ e (renVar r v)) = subVar-∙Ren (σ ∙Sub Ext-to-Sub e) r v

subTm-∙Ren : (σ : Sub Θ Δ) → (r : Ren Δ Γ) → (t : Tm Γ a) → subTm σ (renTm r t) ≡ subTm (σ ∙Sub Ren-to-Sub r) t
subTm-∙Ren σ r (var v)                                                                                                 = subVar-∙Ren σ r v
subTm-∙Ren σ r (lam {a} t) rewrite subTm-∙Ren (keepSub σ) (keepRen r) t | renSub-subSub freshRen[ a ] σ (Ren-to-Sub r) = refl
subTm-∙Ren σ r (app t u)   rewrite subTm-∙Ren σ r t | subTm-∙Ren σ r u                                                 = refl
subTm-∙Ren σ r (box t)     rewrite subTm-∙Ren (keepSub# σ)                  (keepRen# r)    t                          = refl
subTm-∙Ren σ r (unb t e)   rewrite subTm-∙Ren (factorSub (factorExt e r) σ) (factorRen e r) t                          = refl

subSub-∙Ren : (σ : Sub Θ Δ) → (r : Ren Δ Γ) → (τ : Sub Γ Ξ) → σ ∙Sub (renSub r τ) ≡ (σ ∙Sub Ren-to-Sub r) ∙Sub τ
subSub-∙Ren σ r []                                                                             = refl
subSub-∙Ren σ r (τ `, t)   rewrite subSub-∙Ren σ r τ | subTm-∙Ren σ r t                        = refl
subSub-∙Ren σ r (lock τ e) rewrite subSub-∙Ren (factorSub (factorExt e r) σ) (factorRen e r) τ = refl

subTm-∙Ext : (σ : Sub Θ Δ) → (e : Ext Γ Δ) → (t : Tm Γ a) → subTm σ (extTm e t) ≡ subTm (σ ∙Sub Ext-to-Sub e) t
subTm-∙Ext σ e t = subTm-∙Ren σ (Ext-to-Ren e) t

subSub-∙Ext : (σ : Sub Θ Δ) → (e : Ext Γ Δ) → (τ : Sub Γ Ξ) → σ ∙Sub extSub e τ ≡ (σ ∙Sub Ext-to-Sub e) ∙Sub τ
subSub-∙Ext σ e τ rewrite renSub-extSub e τ = subSub-∙Ren σ (Ext-to-Ren e) τ

subVar-∙ : (σ : Sub Θ Δ) → (τ : Sub Δ Γ) → (v : Var Γ a) → subTm σ (subVar τ v) ≡ subVar (σ ∙Sub τ) v
subVar-∙ σ (τ `, t)   zero      = refl
subVar-∙ σ (τ `, t)   (succ  v) = subVar-∙ σ τ v
subVar-∙ σ (lock τ e) (succ# v) rewrite subVar-∙ σ (extSub e τ) v | subSub-∙Ext σ e τ | extSub-∙ (factorExt e σ) (factorSub e σ) τ | factorSub-comm e σ = refl

keepSub-fun-∙ : (a : Ty) → (σ : Sub Θ Δ) → (τ : Sub Δ Γ) → keepSub[ a ] σ ∙Sub keepSub[ a ] τ ≡ keepSub[ a ] (σ ∙Sub τ)
keepSub-fun-∙ a σ τ rewrite subSub-∙Ren (keepSub[ a ] σ) freshRen[ a ] τ | renSub-subSub freshRen[ a ] σ τ = refl

keepSub#-fun-∙ : (σ : Sub Θ Δ) → (τ : Sub Δ Γ) → keepSub# σ ∙Sub keepSub# τ ≡ keepSub# (σ ∙Sub τ)
keepSub#-fun-∙ σ τ = refl

subTm-∙ : (σ : Sub Θ Δ) → (τ : Sub Δ Γ) → (t : Tm Γ a) → subTm σ (subTm τ t) ≡ subTm (σ ∙Sub τ) t
subTm-∙ σ τ (var v)                                                                               = subVar-∙ σ τ v
subTm-∙ σ τ (lam {a} t) rewrite subTm-∙ (keepSub[ a ] σ) (keepSub[ a ] τ) t | keepSub-fun-∙ a σ τ = refl
subTm-∙ σ τ (app t u)   rewrite subTm-∙ σ τ t | subTm-∙ σ τ u                                     = refl
subTm-∙ σ τ (box t)     rewrite subTm-∙ (keepSub# σ)                  (keepSub# τ)    t           = refl
subTm-∙ σ τ (unb t e)   rewrite subTm-∙ (factorSub (factorExt e τ) σ) (factorSub e τ) t           = refl

∙Sub-assoc : (σ : Sub Ξ Θ) → (τ : Sub Θ Δ) → (μ : Sub Δ Γ) → σ ∙Sub (τ ∙Sub μ) ≡ (σ ∙Sub τ) ∙Sub μ
∙Sub-assoc σ τ []                                                                            = refl
∙Sub-assoc σ τ (μ `, t)   rewrite ∙Sub-assoc σ τ μ | subTm-∙ σ τ t                           = refl
∙Sub-assoc σ τ (lock μ e) rewrite ∙Sub-assoc (factorSub (factorExt e τ) σ) (factorSub e τ) μ = refl

extTm-subVar : (e : Ext Δ Θ) → (σ : Sub Δ Γ) → (v : Var Γ a) → extTm e (subVar σ v) ≡ subVar (extSub e σ) v
extTm-subVar e (σ `, t)    zero                                                                  = refl
extTm-subVar e (σ `, t)    (succ  v)                                                             = extTm-subVar e σ v
extTm-subVar e (lock σ e') (succ# v) rewrite extTm-subVar e (extSub e' σ) v | extSub-∙Ext e' e σ = refl

subVar-fun-id : (v : Var Γ a) → subVar idSub v ≡ var v
subVar-fun-id zero                                                                             = refl
subVar-fun-id (succ[ b ] v) rewrite sym (renTm-subVar freshRen[ b ] idSub v) | subVar-fun-id v = refl
subVar-fun-id (succ#     v) rewrite sym (extTm-subVar new idSub v) | subVar-fun-id v           = refl

{-# REWRITE subVar-fun-id #-}

subTm-fun-id : (t : Tm Γ a) → subTm idSub t ≡ t
subTm-fun-id (var v)                                           = refl
subTm-fun-id (lam t)   rewrite subTm-fun-id t                  = refl
subTm-fun-id (app t u) rewrite subTm-fun-id t | subTm-fun-id u = refl
subTm-fun-id (box t)   rewrite subTm-fun-id t                  = refl
subTm-fun-id (unb t e) rewrite subTm-fun-id t                  = refl

{-# REWRITE subTm-fun-id #-}

idSub-unit-left : (σ : Sub Δ Γ) → idSub[ Δ ] ∙Sub σ ≡ σ
idSub-unit-left []                                   = refl
idSub-unit-left (σ `, t)   rewrite idSub-unit-left σ = refl
idSub-unit-left (lock σ e) rewrite idSub-unit-left σ = refl

{-# REWRITE idSub-unit-left #-}

idSub-unit-right : (σ : Sub Δ Γ) → σ ∙Sub idSub[ Γ ] ≡ σ
idSub-unit-right []                                                                                               = refl
idSub-unit-right (σ `, t)   rewrite idSub-unit-right σ | subSub-∙Ren (σ `, t) freshRen idSub | idSub-unit-right σ = refl
idSub-unit-right (lock σ e) rewrite idSub-unit-right σ                                                            = refl

{-# REWRITE idSub-unit-right #-}
