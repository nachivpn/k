open import HEUtil
open import Context using ()
  renaming (Ctx to ICtx ; _⊆_ to I⊆ ; Var to IVar)

module IS4.Substitution (Ty : Set)
  (Tm    : ICtx Ty → Ty → Set)
  (var   : ∀ {Γ a} → IVar Ty Γ a → Tm Γ a)
  (wkTm  : ∀ {Γ' Γ a} → I⊆ Ty Γ Γ' → Tm Γ a → Tm Γ' a)
  where

open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; -,_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_)

open import Context Ty hiding (ext🔒)
open ≡-Reasoning

private
  variable
    a b c d : Ty

-- extension that "generates a new context frame"
new : CExt (Γ 🔒) Γ ([] 🔒) -- Γ R Γ 🔒
new = ext🔒- nil

new[_] = λ Γ → new {Γ}

freshExt : Ext θ (Γ `, a) Γ ([] `, a)
freshExt = ext nil

----------------
-- Substitutions
----------------

data Sub : Ctx → Ctx → Set where
  []   : Sub Δ []
  _`,_ : (σ : Sub Δ Γ) → (t : Tm Δ a) → Sub Δ (Γ `, a)
  lock : (σ : Sub ΔL Γ) → (e : CExt Δ ΔL ΔR) → Sub Δ (Γ 🔒)

variable
  σ σ' σ'' : Sub Δ Γ
  τ τ' τ'' : Sub Δ Γ

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
wkSub w (lock s e)  = lock (wkSub (factorWk e w) s) (factorExt e w)

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

ExtToSub : CExt Γ ΓL ΓR → Sub Γ (ΓL 🔒)
ExtToSub e = lock idₛ e

private

  factor2ₛ : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → ∃ λ ΔL → ∃ λ ΔR → Sub ΔL ΓL × CExt Δ ΔL ΔR
  factor2ₛ nil        s           = -, -, s , nil
  factor2ₛ (ext e)    (s `, _)    = factor2ₛ e s
  factor2ₛ (ext🔒- e) (lock {ΔR = ΔR} s es)  = let (ΔL' , ΔR' , s' , e'') = factor2ₛ e s
    in ΔL' , (ΔR' ,, ΔR) , s' , extRAssoc e'' es

  factor2Subₛ : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Sub _ ΓL
  factor2Subₛ = λ e s → factor2ₛ e s .proj₂ .proj₂ .proj₁

  factor2Extₛ : ∀ (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → CExt Δ _ _
  factor2Extₛ = λ e s → factor2ₛ e s .proj₂ .proj₂ .proj₂

-- "Left" context of factoring with a substitution (see factorExtₛ)
lCtxₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Ctx
lCtxₛ {Δ = Δ} nil       s           = Δ
lCtxₛ         (ext e)   (s `, t)    = lCtxₛ e s
lCtxₛ         (ext🔒- e) (lock s e') = lCtxₛ e s

-- "Right" context of factoring with a substitution (see factorExtₛ)
rCtxₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Ctx
rCtxₛ nil       s                     = []
rCtxₛ (ext e)   (s `, t)              = rCtxₛ e s
rCtxₛ (ext🔒- e) (lock {ΔR = ΔR} s e') = rCtxₛ e s ,, ΔR

-- same as factor2Extₛ
factorExtₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → CExt Δ (lCtxₛ e s) (rCtxₛ e s)
factorExtₛ nil       s           = nil
factorExtₛ (ext e)   (s `, _)    = factorExtₛ e s
factorExtₛ (ext🔒- e) (lock s e') = extRAssoc (factorExtₛ e s) e'

-- same as factor2Subₛ
factorSubₛ : (e : CExt Γ ΓL ΓR) (s : Sub Δ Γ) → Sub (lCtxₛ e s) ΓL
factorSubₛ nil       s           = s
factorSubₛ (ext e)   (s `, t)    = factorSubₛ e s
factorSubₛ (ext🔒- e) (lock s e') = factorSubₛ e s

-- Left context of weakening and applying a substituion
-- is the same as the
-- Left context of applying and then weakening it
lCtxₛ-lCtx-comm : (e  : CExt Γ ΓL ΓR) (w  : Δ ⊆ Δ') (s  : Sub Δ Γ)
  → lCtxₛ e (wkSub w s) ≡ lCtx (factorExtₛ e s) w
lCtxₛ-lCtx-comm nil       w s           = refl
lCtxₛ-lCtx-comm (ext e)   w (s `, _)    = lCtxₛ-lCtx-comm e w s
lCtxₛ-lCtx-comm (ext🔒- e) w (lock s e') = trans
  (lCtxₛ-lCtx-comm e (factorWk e' w) s)
  (sym (lCtxPresTrans (factorExtₛ e _) e' _))

-- Right context of weakening and applying a substituion
-- is the same as the
-- Right context of applying and then weakening it
rCtxₛ-rCtx-comm : (e  : CExt Γ ΓL ΓR) (w  : Δ ⊆ Δ') (s  : Sub Δ Γ)
  → rCtxₛ e (wkSub w s) ≡ rCtx (factorExtₛ e s) w
rCtxₛ-rCtx-comm nil w s                 = refl
rCtxₛ-rCtx-comm (ext e) w (s `, _)      = rCtxₛ-rCtx-comm e w s
rCtxₛ-rCtx-comm (ext🔒- e) w (lock s e') = trans
  (cong₂ _,,_ (rCtxₛ-rCtx-comm e (factorWk e' w) s) refl)
  (sym (rCtxPresTrans (factorExtₛ e _) e' _))

-- Weakening and factoring a subtitution can be achieved by factoring and then weakening it
factorSubₛ-wkSub-comm : (e :  CExt Γ ΓL ΓR) (s  : Sub Δ Γ) (w : Δ ⊆ Δ')
  → subst (λ ΔL → Sub ΔL ΓL) (lCtxₛ-lCtx-comm e w s) (factorSubₛ e (wkSub w s)) ≡ wkSub (factorWk (factorExtₛ e s) w) (factorSubₛ e s)
factorSubₛ-wkSub-comm nil       s           w = refl
factorSubₛ-wkSub-comm (ext e)   (s `, t)    w = factorSubₛ-wkSub-comm e s w
factorSubₛ-wkSub-comm (ext🔒- e) (lock s e') w = begin
  subst (λ ΔL → Sub ΔL _)
    (trans (lCtxₛ-lCtx-comm e _ _) (sym (lCtxPresTrans _ e' _)))
    (factorSubₛ e (wkSub (factorWk e' w) s))
    -- split `subst _ (trans p q) ...` to `subst _ q (subst _ p ...)`
    ≡⟨ sym (subst-subst (lCtxₛ-lCtx-comm e _ _)) ⟩
  subst (λ ΔL → Sub ΔL _)
    (sym (lCtxPresTrans _ e' _))
    (subst (λ ΔL → Sub ΔL _) (lCtxₛ-lCtx-comm e _ _)
      (factorSubₛ e (wkSub (factorWk e' w) s)))
    -- rewrite inner subst
    ≡⟨ cong (subst (λ ΔL → Sub ΔL _) _) (factorSubₛ-wkSub-comm e s (factorWk e' w)) ⟩
  subst (λ ΔL → Sub ΔL _)
    (sym (lCtxPresTrans _ e' _))
    (wkSub (factorWk (factorExtₛ e s) (factorWk e' w)) (factorSubₛ e s))
    -- remove subst and apply factorWkPresTrans
    ≅⟨ HE.trans (≡-subst-removable _ _ _) factorWkPresTrans-under-wkSub ⟩
 wkSub (factorWk (extRAssoc (factorExtₛ e s) e') w) (factorSubₛ e s) ∎
 where
   factorWkPresTrans-under-wkSub : wkSub (factorWk (factorExtₛ e s) (factorWk e' w)) _ ≅ wkSub (factorWk (extRAssoc (factorExtₛ e s) e') w) _
   factorWkPresTrans-under-wkSub = HE.icong (_ ⊆_) (sym (lCtxPresTrans _ e' _)) (λ s' → wkSub s' _)
     (HE.sym (HE.trans (≡-subst-addable _ _ _) (≡-to-≅ (factorWkPresTrans _ e' _))))

-- factorExtₛ counterpart of factorSubₛ-wkSub-comm
factorExtₛ-wkSub-comm : (e :  CExt Γ ΓL ΓR) (s  : Sub Δ Γ) (w : Δ ⊆ Δ')
  → subst₂ (CExt Δ') (lCtxₛ-lCtx-comm e w s) (rCtxₛ-rCtx-comm e w s) (factorExtₛ e (wkSub w s)) ≡ factorExt (factorExtₛ e s) w
factorExtₛ-wkSub-comm _ _ _ = ExtIsProp _ _

lCtxₛ-factorExt-trimSub-assoc : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
   → lCtxₛ e (trimSub w s) ≡ lCtxₛ (factorExt e w) s
lCtxₛ-factorExt-trimSub-assoc nil       s          w
  = refl
lCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, _)   (drop w)
  = lCtxₛ-factorExt-trimSub-assoc (ext e) s w
lCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, _)   (keep w)
  = lCtxₛ-factorExt-trimSub-assoc e s w
lCtxₛ-factorExt-trimSub-assoc (ext🔒- e) (s `, t)   (drop w)
  = lCtxₛ-factorExt-trimSub-assoc (ext🔒- e) s w
lCtxₛ-factorExt-trimSub-assoc (ext🔒- e) (lock s _) (keep🔒 w)
  = lCtxₛ-factorExt-trimSub-assoc e s w

rCtxₛ-factorExt-trimSub-assoc : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
   → rCtxₛ e (trimSub w s) ≡ rCtxₛ (factorExt e w) s
rCtxₛ-factorExt-trimSub-assoc nil       s          w
  = refl
rCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, t)   (drop w)
  = rCtxₛ-factorExt-trimSub-assoc (ext e) s w
rCtxₛ-factorExt-trimSub-assoc (ext e)   (s `, t)   (keep w)
  = rCtxₛ-factorExt-trimSub-assoc e s w
rCtxₛ-factorExt-trimSub-assoc (ext🔒- e) (s `, t)   (drop w)
  = rCtxₛ-factorExt-trimSub-assoc (ext🔒- e) s w
rCtxₛ-factorExt-trimSub-assoc (ext🔒- e) (lock s _) (keep🔒 w)
  = cong (_,, _) (rCtxₛ-factorExt-trimSub-assoc e s w)

factorSubₛ-trimSub-comm : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → subst (λ ΔL → Sub ΔL _) (lCtxₛ-factorExt-trimSub-assoc e s w) (factorSubₛ e (trimSub w s)) ≡ trimSub (factorWk e w) (factorSubₛ (factorExt e w) s)
factorSubₛ-trimSub-comm nil       s          w
  = refl
factorSubₛ-trimSub-comm (ext e)   (s `, _)   (drop w)
  = factorSubₛ-trimSub-comm (ext e) s w
factorSubₛ-trimSub-comm (ext e)   (s `, _)   (keep w)
  = factorSubₛ-trimSub-comm e s w
factorSubₛ-trimSub-comm (ext🔒- e) (s `, t)   (drop w)
  = factorSubₛ-trimSub-comm (ext🔒- e) s w
factorSubₛ-trimSub-comm (ext🔒- e) (lock s _) (keep🔒 w)
  = factorSubₛ-trimSub-comm e s w

factorExtₛ-trimSub-comm : (e : CExt Γ ΓL ΓR) (s : Sub Δ' Δ) (w : Γ ⊆ Δ)
  → subst₂ (CExt Δ') (lCtxₛ-factorExt-trimSub-assoc e s w) (rCtxₛ-factorExt-trimSub-assoc e s w) (factorExtₛ e (trimSub w s)) ≡ factorExtₛ (factorExt e w) s
factorExtₛ-trimSub-comm _ _ _ = ExtIsProp _ _

---------------------------------------------
-- Factorisation of the identity substitution
---------------------------------------------

←🔒₁rCtx : (e : CExt Γ ΓL ΓR) → Ctx
←🔒₁rCtx nil             = []
←🔒₁rCtx (ext {a = a} e) = ←🔒₁rCtx e ,, rCtx′ (factorExtₛ e idₛ) (freshExt {a = a})
←🔒₁rCtx (ext🔒- e)       = ←🔒₁rCtx e

private

  ex : {a b c : Ty} → CExt (ΓL `, a `, b 🔒 `, c 🔒) ΓL ([] `, a `, b 🔒 `, c 🔒)
  ex {Γ} {a} {b} {c} = ext🔒- (ext {a = c} (ext🔒- (ext {a = b} (ext {Γ = Γ} {a = a} nil))))

  _ : ←🔒₁rCtx (ex {ΓL} {c = c}) ≡ [] `, a `, b
  _ = refl

-- Given `e` that ΓL extends Γ, ΓL is a lock-free extension of `lCtxₛ e idₛ`.
-- This means that ΓL ⊆ (lCtxₛ e idₛ), and thus applying `factorSubₛ e idₛ` weakens
-- a term with variables in `←🔒₁rCtx e`
factorSubₛIdWk : (e : CExt Γ ΓL ΓR) → LFExt (lCtxₛ e idₛ) ΓL (←🔒₁rCtx e)
factorSubₛIdWk nil             = nil
factorSubₛIdWk {ΓR = ΓR `, a} (ext {a = .a} e) = subst
  (λ Γ → LFExt Γ _ (←🔒₁rCtx (ext e))) (sym ((lCtxₛ-lCtx-comm e fresh idₛ)))
  (extRAssoc (factorSubₛIdWk e) (factorDropsWk (factorExtₛ e idₛ) freshExt))
factorSubₛIdWk (ext🔒- e)       = factorSubₛIdWk e

-- Obs: Deliberately named _Wk instead of _LFExt

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
