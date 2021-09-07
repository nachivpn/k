open import Context using ()
  renaming (Ctx to ICtx ; _≤_ to I≤ ; Var to IVar)

module IS4.Substitution (Ty : Set)
  (Tm    : ICtx Ty → Ty → Set)
  (var   : ∀ {Γ a} → IVar Ty Γ a → Tm Γ a)
  (wkTm  : ∀ {Γ' Γ a} → I≤ Ty Γ' Γ → Tm Γ a → Tm Γ' a)
  where

open import Data.Unit using (tt)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Context Ty

private
  variable
    a b c d : Ty

----------------
-- Substitutions
----------------

data Sub : Ctx → Ctx → Set where
  []   : Sub Δ []
  _`,_ : Sub Δ Γ → Tm Δ a → Sub Δ (Γ `, a)
  lock : Sub ΔL Γ → Ext tt Δ ΔL ΔR → Sub Δ (Γ 🔒)

-- composition operation for weakening after substituion
trimSub : Γ ≤ Δ → Sub Γ' Γ → Sub Γ' Δ
trimSub base      []         = []
trimSub (drop w)  (s `, x)   = trimSub w s
trimSub (keep w)  (s `, x)   = (trimSub w s) `, x
trimSub (keep🔒 w) (lock s x) = lock (trimSub w s) x

-- apply substitution to a variable
substVar : Sub Γ Δ → Var Δ a → Tm Γ a
substVar (s `, t) ze     = t
substVar (s `, t) (su x) = substVar s x

-- weaken a substitution
wkSub : Γ' ≤ Γ → Sub Γ Δ → Sub Γ' Δ
wkSub w []          = []
wkSub w (s `, t)    = (wkSub w s) `, wkTm w t
wkSub w (lock s e)  = lock (wkSub (sliceLeftG e w) s) (wkExt e w)

-- identity substitution
idₛ : Sub Γ Γ
idₛ {[]}     = []
idₛ {Γ `, x} = wkSub fresh idₛ `, (var ze)
idₛ {Γ 🔒}    = lock (idₛ {Γ}) (ext🔒 tt nil)

-- NOTE: composition requires parallel substituion for terms

-- "drop" the last variable in the context
dropₛ : Sub Γ Δ → Sub (Γ `, a) Δ
dropₛ s = wkSub fresh s

-- "keep" the last variable in the context
keepₛ : Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
keepₛ s = dropₛ s `, var ze

-- embed a weakening to substitution
embWk : Γ ≤ Δ → Sub Γ Δ
embWk base      = []
embWk (drop w)  = dropₛ (embWk w)
embWk (keep w)  = keepₛ (embWk w)
embWk (keep🔒 w) = lock (embWk w) (ext🔒 tt nil)

ExtToSub : Ext tt Γ ΓL ΓR → Sub Γ (ΓL 🔒)
ExtToSub e = lock idₛ e

--------------------
-- Substitution laws
--------------------

-- NOTE: these are only the laws that follow directly from the structure of substitutions
coh-trimSub-wkVar : (x : Var Γ a) (s : Sub Δ' Δ) (w : Δ ≤ Γ)
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
nat-substVar : (x : Var Γ a) (s : Sub Δ Γ) (w : Δ' ≤ Δ)
  → substVar (wkSub w s) x ≡ wkTm w (substVar s x)
nat-substVar ze     (s `, t) w = refl
nat-substVar (su x) (s `, t) w = nat-substVar x s w

-- naturality of trimSub
nat-trimSub : (s : Sub Γ Δ) (w : Δ ≤ Δ') (w' : Γ' ≤ Γ)
  → wkSub w' (trimSub w s) ≡ trimSub w (wkSub w' s)
nat-trimSub []         base      w' = refl
nat-trimSub (s `, t)   (drop w)  w' = nat-trimSub s w w'
nat-trimSub (s `, t)   (keep w)  w' = cong (_`, wkTm w' t) (nat-trimSub s w w')
nat-trimSub (lock s x) (keep🔒 w) w' = cong₂ lock (nat-trimSub s w _) refl

-- `trimSub` on the identity substituion embeds the weakening
trimSubId : (w : Δ ≤ Γ) → trimSub w idₛ ≡ embWk w
trimSubId base = refl
trimSubId (drop w) = trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w))
trimSubId (keep w) = cong (_`, var ze) (trans
  (sym (nat-trimSub idₛ w fresh))
  (cong (wkSub fresh) (trimSubId w)))
trimSubId (keep🔒 w) = cong₂ lock (trimSubId w) refl
