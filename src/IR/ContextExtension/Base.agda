{-# OPTIONS --safe --without-K #-}
module IR.ContextExtension.Base (Ty : Set) where

open import Data.Product using (Σ ; _×_) renaming (proj₁ to fst ; proj₂ to snd)

open import Context.Base Ty

data Ext : (Γ Δ : Ctx) → Set where                   -- Δ → Γ #
  new[_] : (Γ : Ctx) → Ext Γ (Γ #)                   -- id
  ext[_] : (a : Ty) → (e : Ext Γ Δ) → Ext Γ (Δ `, a) -- fresh ; e
  ext#-  : (e : Ext Γ Δ) → Ext Γ (Δ #)               -- ε ; e

pattern new {Γ}   = new[ Γ ]
pattern ext {a} e = ext[ a ] e

variable
  e e' e'' : Ext Γ Δ

record Factor (S : (Γ Δ : Ctx) → Set) : Set where
  field
    factor : (e : Ext Γ Δ) → (s : S Θ Δ) → Σ Ctx λ Θ' → S Θ' Γ × Ext Θ' Θ

  factorCtx : (e : Ext Γ Δ) → (s : S Θ Δ) → Ctx
  factorCtx e s = factor e s .fst

  factorS : (e : Ext Γ Δ) → (s : S Θ Δ) → S (factorCtx e s) Γ
  factorS e s = factor e s .snd .fst

  factorExt : (e : Ext Γ Δ) → (s : S Θ Δ) → Ext (factorCtx e s) Θ
  factorExt e s = factor e s .snd .snd

open Factor {{...}} public using (factorCtx ; factorExt)

-- R structure for extensions
-- \.<C-g>Ext
_∙Ext_ : (e : Ext Γ Δ) → (e' : Ext Δ Θ) → Ext Γ Θ -- e ∘ (ε ∘ e')
e ∙Ext new[ Γ ]    = ext#- e
e ∙Ext ext[ a ] e' = ext[ a ] (e ∙Ext e')
e ∙Ext ext#-    e' = ext#-    (e ∙Ext e')
-- /R structure for extensions
