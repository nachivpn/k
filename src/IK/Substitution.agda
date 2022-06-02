{-# OPTIONS --safe --with-K #-}
open import Context using ()
  renaming (Ctx to ICtx ; _⊆_ to I⊆ ; Var to IVar)

module IK.Substitution (Ty : Set)
  (Tm    : ICtx Ty → Ty → Set)
  (var   : ∀ {Γ a} → IVar Ty Γ a → Tm Γ a)
  (wkTm  : ∀ {Γ' Γ a} → I⊆ Ty Γ Γ' → Tm Γ a → Tm Γ' a)
  where

open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; -,_)

open import Relation.Binary.PropositionalEquality

open import Context (Ty)

private
  variable
    a b c d : Ty

-- extension that "generates a new context frame"
new : LFExt (Γ 🔒) (Γ 🔒) [] -- Γ R Γ 🔒
new = nil

new[_] = λ Γ → new {Γ}

----------------
-- Substitutions
----------------

data Sub : Ctx → Ctx → Set where
  []   : Sub Δ []
  _`,_ : (σ : Sub Δ Γ) → (t : Tm Δ a) → Sub Δ (Γ `, a)
  lock : (σ : Sub ΔL Γ) → (e : LFExt Δ (ΔL 🔒) ΔR) → Sub Δ (Γ 🔒)

-- composition operation for weakening after substitution
trimSub : Δ ⊆ Γ → Sub Γ' Γ → Sub Γ' Δ
trimSub base      []         = []
trimSub (drop w)  (s `, x)   = trimSub w s
trimSub (keep w)  (s `, x)   = (trimSub w s) `, x
trimSub (keep🔒 w) (lock s x) = lock (trimSub w s) x

-- apply substitution to a variable
substVar : Sub Γ Δ → Var Δ a → Tm Γ a
substVar (s `, t) ze     = t
substVar (s `, t) (su x) = substVar s x

-- weaken a substitution
wkSub : Γ ⊆ Γ' → Sub Γ Δ → Sub Γ' Δ
wkSub w []          = []
wkSub w (s `, t)    = (wkSub w s) `, wkTm w t
wkSub w (lock s e)  = lock (wkSub (sliceLeft e w) s) (wkLFExt e w)

-- NOTE: composition requires parallel substitution for terms

-- "drop" the last variable in the context
dropₛ : Sub Γ Δ → Sub (Γ `, a) Δ
dropₛ s = wkSub fresh s

-- "keep" the last variable in the context
keepₛ : Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
keepₛ s = dropₛ s `, var ze

-- "keep" the lock in the context
keep🔒ₛ : Sub Γ Δ → Sub (Γ 🔒) (Δ 🔒)
keep🔒ₛ s = lock s new

-- embed a weakening to substitution
embWk : Δ ⊆ Γ → Sub Γ Δ
embWk base      = []
embWk (drop w)  = dropₛ (embWk w)
embWk (keep w)  = keepₛ (embWk w)
embWk (keep🔒 w) = keep🔒ₛ (embWk w)

-- identity substitution
idₛ : Sub Γ Γ
idₛ = embWk idWk

idₛ[_] = λ Γ → idₛ {Γ}

private
  factorₛ : ∀ (e : LFExt Γ (ΓL 🔒) ΓR) (s : Sub Δ Γ) → ∃ λ ΔL → ∃ λ ΔR → Sub ΔL ΓL × LFExt Δ (ΔL 🔒) ΔR
  factorₛ nil     (lock s e) = -, -, s , e
  factorₛ (ext e) (s `, t)   = factorₛ e s

factorSubₛ : ∀ (e : LFExt Γ (ΓL 🔒) ΓR) (s : Sub Δ Γ) → Sub _ ΓL
factorSubₛ = λ e s → factorₛ e s .proj₂ .proj₂ .proj₁

factorExtₛ : ∀ (e : LFExt Γ (ΓL 🔒) ΓR) (s : Sub Δ Γ) → LFExt Δ _ _
factorExtₛ = λ e s → factorₛ e s .proj₂ .proj₂ .proj₂

--------------------
-- Substitution laws
--------------------

-- NOTE: these are only the laws that follow directly from the structure of substitutions
coh-trimSub-wkVar : (x : Var Γ a) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → substVar (trimSub w s) x ≡ substVar s (wkVar w x)
coh-trimSub-wkVar ze (s `, x) (drop w)
  = coh-trimSub-wkVar ze s w
coh-trimSub-wkVar ze (s `, x) (keep w)
  = refl
coh-trimSub-wkVar (su x) (s `, x₁) (drop w)
  = coh-trimSub-wkVar (su x) s w
coh-trimSub-wkVar (su x) (s `, x₁) (keep w)
  = coh-trimSub-wkVar x s w

-- `trimSub` preserves the identity
trimSubPresId : (s : Sub Δ Γ) → trimSub idWk s ≡ s
trimSubPresId []         = refl
trimSubPresId (s `, x)   = cong (_`, _) (trimSubPresId s)
trimSubPresId (lock s x) = cong₂ lock (trimSubPresId s) refl

-- naturality of substVar
nat-substVar : (x : Var Γ a) (s : Sub Δ Γ) (w : Δ ⊆ Δ')
  → substVar (wkSub w s) x ≡ wkTm w (substVar s x)
nat-substVar ze     (s `, t) w = refl
nat-substVar (su x) (s `, t) w = nat-substVar x s w

-- naturality of trimSub
nat-trimSub : (s : Sub Γ Δ) (w : Δ' ⊆ Δ) (w' : Γ ⊆ Γ')
  → wkSub w' (trimSub w s) ≡ trimSub w (wkSub w' s)
nat-trimSub []         base      w' = refl
nat-trimSub (s `, t)   (drop w)  w' = nat-trimSub s w w'
nat-trimSub (s `, t)   (keep w)  w' = cong (_`, wkTm w' t) (nat-trimSub s w w')
nat-trimSub (lock s x) (keep🔒 w) w' = cong₂ lock (nat-trimSub s w _) refl

-- `trimSub` on the identity substitution embeds the weakening
trimSubId : (w : Γ ⊆ Δ) → trimSub w idₛ ≡ embWk w
trimSubId base = refl
trimSubId (drop w) = trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w))
trimSubId (keep w) = cong (_`, var ze) (trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w)))
trimSubId (keep🔒 w) = cong₂ lock (trimSubId w) refl
