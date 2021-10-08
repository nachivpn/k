{-# OPTIONS --allow-unsolved-metas #-}
module IS4.Term.Properties where

open import Data.Product using (∃; _,_) renaming (_×_ to _∧_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂; respˡ; respʳ)

open import IS4.Term.Base
open import IS4.Term.Conversion
open import IS4.Term.Reduction

private
  variable
    v v' v'' : Var Γ a
    μ μ' μ'' : Sub Δ Γ

wkTm-pres-⟶ : ∀ (w : Γ ⊆ Γ') → (t⟶t' : t ⟶ t') → wkTm w t ⟶ wkTm w t'
wkTm-pres-⟶ w (red-fun t u)          = respʳ _⟶_ {!!} (red-fun (wkTm (keep w) t) (wkTm w u))
wkTm-pres-⟶ w (exp-fun t)            = respʳ _⟶_ {!!} (exp-fun (wkTm w t))
wkTm-pres-⟶ w (red-box t e)          = respʳ _⟶_ {!!} (red-box (wkTm (keep🔒 (factor2≤ e w)) t) (factor2Ext e w))
wkTm-pres-⟶ w (exp-box t)            = exp-box (wkTm w t)
wkTm-pres-⟶ w (cong-lam r)           = cong-lam   (wkTm-pres-⟶ (keep   w) r)
wkTm-pres-⟶ w (cong-box r)           = cong-box   (wkTm-pres-⟶ (keep🔒 w) r)
wkTm-pres-⟶ w (cong-unbox {e = e} r) = cong-unbox (wkTm-pres-⟶ (factor2≤ e w) r)
wkTm-pres-⟶ w (cong-app1 r)          = cong-app1  (wkTm-pres-⟶ w r)
wkTm-pres-⟶ w (cong-app2 r)          = cong-app2  (wkTm-pres-⟶ w r)

wkTm-pres-⟶* : ∀ (w : Γ ⊆ Γ') → (t⟶*t' : t ⟶* t') → wkTm w t ⟶* wkTm w t'
wkTm-pres-⟶* w = cong-⟶-to-cong-⟶* (wkTm-pres-⟶ w)

wkTm-pres-≈ : ∀ (w : Γ ⊆ Γ') → (t≈t' : t ≈ t') → wkTm w t ≈ wkTm w t'
wkTm-pres-≈ w = cong-⟶-to-cong-≈ (wkTm-pres-⟶ w)

wkTm-pres-id : (t : Tm Γ a) → wkTm idWk t ≡ t
wkTm-pres-id (var x) = cong var (wkVarPresId x)
wkTm-pres-id (lam t) = cong lam (wkTm-pres-id t)
wkTm-pres-id (app t u) = cong₂ app (wkTm-pres-id t) (wkTm-pres-id u)
wkTm-pres-id (box t) = cong box (wkTm-pres-id t)
wkTm-pres-id (unbox t e) = {!with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
wkTm-pres-id (unbox t e) | refl | refl = cong₂ unbox
  (trans (cong₂ wkTm (sliceLeftId e) refl) (wkTmPresId t))
  (wkLFExtPresId e)!}

wkSub-pres-id : (s : Sub Γ Δ) → wkSub idWk s ≡ s
wkSub-pres-id [] = refl
wkSub-pres-id (s `, t) = cong₂ _`,_ (wkSub-pres-id s) (wkTm-pres-id t)
wkSub-pres-id (lock s e) = {!with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
... | refl | refl = cong₂ lock
  (trans (cong₂ wkSub (sliceLeftId e) refl) (wkSubPresId s))
  (wkLFExtPresId e)!}

-- weakening of terms (a functor map) preserves weakening composition
wkTm-pres-∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (t : Tm Γ a) → wkTm w' (wkTm w t) ≡ wkTm (w ∙ w') t
wkTm-pres-∙ w w' (var x)   = cong  var (wkVarPres∙ w w' x)
wkTm-pres-∙ w w' (lam t)   = cong  lam (wkTm-pres-∙ (keep w) (keep w') t)
wkTm-pres-∙ w w' (app t u) = cong₂ app (wkTm-pres-∙ w w' t) (wkTm-pres-∙ w w' u)
wkTm-pres-∙ w w' (box t)   = cong  box (wkTm-pres-∙ (keep🔒 w) (keep🔒 w') t)
wkTm-pres-∙ w w' (unbox t e) = {!cong₂ unbox
  (trans (wkTmPres∙ _ _ _) (cong₂ wkTm (sliceLeftPres∙ w' w e) refl)) (wkLFExtPres∙  w' w e)!}

-- weakening of substitutions preserves weakening compisition
wkSub-pres-∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (s : Sub Γ ΓR) → wkSub w' (wkSub w s) ≡ wkSub (w ∙ w') s
wkSub-pres-∙ w w' []       = refl
wkSub-pres-∙ w w' (s `, t) = cong₂ _`,_ (wkSub-pres-∙ w w' s) (wkTm-pres-∙ w w' t)
wkSub-pres-∙ w w' (lock s e) = {!cong₂ lock
  (trans  (wkSubPres∙ _ _ s) (cong₂ wkSub (sliceLeftPres∙ w' w e) refl))
  (wkLFExtPres∙  w' w e)!}

--------------------
-- Substitution laws
--------------------

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

embWkVar : var (wkVar w v) ≡ substVar (embWk w) v
embWkVar = {!!}

embWk-pres-factor2 : ∀ (e : CExt Δ ΓL ΓR) (w : Δ ⊆ Δ') → _≡_ {A = ∃ λ ΓL' → ∃ λ ΓR' → Sub ΓL' ΓL ∧ CExt Δ' ΓL' ΓR'} (f2LCtx e w , f2RCtx e w , embWk (factor2≤ e w) , factor2Ext e w) (f2LCtxₛ e (embWk w) , f2RCtxₛ e (embWk w) , factor2Sub e (embWk w) , factor2Extₛ e (embWk w))
embWk-pres-factor2 nil         w                = refl
embWk-pres-factor2 e@(ext _)   (drop {a = a} w) = {!!}
embWk-pres-factor2 e@(ext🔒- _) (drop {a = a} w) = {!!}
embWk-pres-factor2 (ext e)     (keep {a = a} w) = {!!}
embWk-pres-factor2 e@(ext🔒- _) (keep🔒 w)        = {!!}

embWkTm : wkTm w t ≡ substTm (embWk w) t
embWkTm {w = w} {t = var v}         = embWkVar
embWkTm {w = w} {t = lam t}         = cong lam (embWkTm {t = t})
embWkTm {w = w} {t = app t u}       = cong₂ app (embWkTm {t = t}) (embWkTm {t = u})
embWkTm {w = w} {t = box t}         = cong box (embWkTm {t = t})
embWkTm {w = w} {t = unbox {Γ} t e} = h (embWk-pres-factor2 e w)
  where
    h : ∀ {Δ' : Ctx}
          {f2LCtxew f2RCtxew : Ctx}             {factor2≤ew : Γ ⊆ f2LCtxew}                {factor2Extew : CExt Δ' f2LCtxew f2RCtxew}
          {f2LCtxₛeembWkw f2RCtxₛeembWkw : Ctx} {factor2SubeembWkw : Sub f2LCtxₛeembWkw Γ} {factor2ExtₛeembWkw : CExt Δ' f2LCtxₛeembWkw f2RCtxₛeembWkw}
          (_p : (f2LCtxew , f2RCtxew , embWk factor2≤ew , factor2Extew) ≡ (f2LCtxₛeembWkw , f2RCtxₛeembWkw , factor2SubeembWkw , factor2ExtₛeembWkw))
        → unbox (wkTm factor2≤ew t) factor2Extew ≡ unbox (substTm factor2SubeembWkw t) factor2ExtₛeembWkw
    h refl = cong₂ unbox embWkTm refl

embWkSub : wkSub w σ ≡ σ ∙ₛ embWk w
embWkSub {w = w} {σ = []}           = refl
embWkSub {w = w} {σ = σ `, t}       = cong₂ _`,_ embWkSub embWkTm
embWkSub {w = w} {σ = lock {Γ} σ e} = h (embWk-pres-factor2 e w)
  where
    h : ∀ {Δ' : Ctx}
          {f2LCtxew f2RCtxew : Ctx}             {factor2≤ew : Γ ⊆ f2LCtxew}                {factor2Extew : CExt Δ' f2LCtxew f2RCtxew}
          {f2LCtxₛeembWkw f2RCtxₛeembWkw : Ctx} {factor2SubeembWkw : Sub f2LCtxₛeembWkw Γ} {factor2ExtₛeembWkw : CExt Δ' f2LCtxₛeembWkw f2RCtxₛeembWkw}
          (_p : (f2LCtxew , f2RCtxew , embWk factor2≤ew , factor2Extew) ≡ (f2LCtxₛeembWkw , f2RCtxₛeembWkw , factor2SubeembWkw , factor2ExtₛeembWkw))
        → lock (wkSub factor2≤ew σ) factor2Extew ≡ lock (σ ∙ₛ factor2SubeembWkw) factor2ExtₛeembWkw
    h refl = cong₂ lock embWkSub refl

embWk-pres-id : embWk idWk[ Γ ] ≡ idₛ
embWk-pres-id = refl

embWk-pres-drop : embWk (drop {a = a} w) ≡ dropₛ (embWk w)
embWk-pres-drop = refl

embWk-pres-keep : embWk (keep {a = a} w) ≡ keepₛ (embWk w)
embWk-pres-keep = refl

embWk-pres-keep🔒 : embWk (keep🔒 w) ≡ keep🔒ₛ (embWk w)
embWk-pres-keep🔒 = refl
