{-# OPTIONS --safe --without-K #-}
module IR.ContextExtension.Properties (Ty : Set) where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import Context.Base             Ty
open import IR.ContextExtension.Base Ty

∙Ext-assoc : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → (e'' : Ext Θ Ξ) → (e ∙Ext e') ∙Ext e'' ≡ e ∙Ext (e' ∙Ext e'')
∙Ext-assoc e e' new[ Θ ]       = refl
∙Ext-assoc e e' (ext[ a ] e'') = cong ext[ a ] (∙Ext-assoc e e' e'')
∙Ext-assoc e e' (ext#-    e'') = cong ext#-    (∙Ext-assoc e e' e'')
