{-# OPTIONS --allow-unsolved-metas #-}
module IS4.NbE.Reification where

open import Data.Unit    using (⊤; tt)          renaming ()
open import Data.Product using (Σ; ∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; module ≡-Reasoning)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import IS4.NbE.Model

open import IS4.Term

private
  P : (a : Ty) → {Γ : Ctx} → (t : Tm Γ a) → (x : Ty' Γ a) → Set
  P 𝕓       {_Γ} t n                             = embNe n ≈ t
  P (a ⇒ b) {Γ}  t (elem f _f-pres-≋ _f-natural) = ∀ {Γ' : Ctx} (w : Γ ⊆ Γ') (u : Tm Γ' a) (x : Ty' Γ' a) (_p : P a u x) → P b (app (wkTm w t) u) (f w x)
  P (◻ a)   {Γ}  t g                             = ∀ {Γ' Δ ΓR' : Ctx} (w : Γ ⊆ Γ') (e : CExt Δ Γ' ΓR') → P a (unbox (wkTm w t) e) (g .apply w (-, e))

  P-invar-⟶ : ∀ (a : Ty) {t t' : Tm Γ a} (t⟶t' : t ⟶ t') {x : Ty' Γ a} → P a t x → P a t' x
  P-invar-⟶ 𝕓       t⟶t' p = ≈-trans p (⟶-to-≈ t⟶t')
  P-invar-⟶ (a ⇒ b) t⟶t' p = λ w u y q → P-invar-⟶ b (cong-app1 (wkTm-pres-⟶ w t⟶t')) (p w u y q)
  P-invar-⟶ (◻ a)   t⟶t' p = λ w e → P-invar-⟶ a (cong-unbox (wkTm-pres-⟶ w t⟶t')) (p w e)

  P-invar-⟵ : ∀ (a : Ty) {t t' : Tm Γ a} (t⟵t' : t' ⟶ t) {x : Ty' Γ a} → P a t x → P a t' x
  P-invar-⟵ 𝕓       t⟵t' p = ≈-trans p (⟵-to-≈ t⟵t')
  P-invar-⟵ (a ⇒ b) t⟵t' p = λ w u y q → P-invar-⟵ b (cong-app1 (wkTm-pres-⟶ w t⟵t')) (p w u y q)
  P-invar-⟵ (◻ a)   t⟵t' p = λ w e → P-invar-⟵ a (cong-unbox (wkTm-pres-⟶ w t⟵t')) (p w e)

  -- XXX: fold
  P-invar-≈ : ∀ (a : Ty) {t t' : Tm Γ a} (t≈t' : t ≈ t') {x : Ty' Γ a} (_p : P a t x) → P a t' x
  P-invar-≈ a ε                     p = p
  P-invar-≈ a (inj₁ t⟶t'' ◅ t''≈t') p = P-invar-≈ a t''≈t' (P-invar-⟶ a t⟶t'' p)
  P-invar-≈ a (inj₂ t⟵t'' ◅ t''≈t') p = P-invar-≈ a t''≈t' (P-invar-⟵ a t⟵t'' p)

  P-invar-≈˘ : ∀ (a : Ty) {t t' : Tm Γ a} (t'≈t : t' ≈ t) {x : Ty' Γ a} (_p : P a t x) → P a t' x
  P-invar-≈˘ a t'≈t p = P-invar-≈ a (≈-sym t'≈t) p

  P-invar-≋ : ∀ (a : Ty) {t : Tm Γ a} {x x' : Ty' Γ a} (x≋x' : x ≋[ evalTy a ] x') (_p : P a t x) → P a t x'
  P-invar-≋ 𝕓       x≋x' p = ≈-trans (≡˘-to-≈ (cong embNe x≋x')) p
  P-invar-≋ (a ⇒ b) x≋x' p = λ w u y q → P-invar-≋ b (x≋x' .pw w y) (p w u y q)
  P-invar-≋ (◻ a)   x≋x' p = λ w e → P-invar-≋ a (x≋x' .pw w (-, e)) (p w e)

  P-invar-≈-≋ : ∀ (a : Ty) {t t' : Tm Γ a} (t≈t' : t ≈ t') {x x' : Ty' Γ a} (x≋x' : x ≋[ evalTy a ] x') (_p : P a t x) → P a t' x'
  P-invar-≈-≋ = {!!}

  P-invar-⊆ : ∀ (a : Ty) (w : Γ ⊆ Γ') {t : Tm Γ a} {x : Ty' Γ a} (_p : P a t x) → P a (wkTm w t) (wkTy' {a = a} w x)
  P-invar-⊆ 𝕓       w {t = t} {x = n} p = let open EqReasoning (Tm-setoid _ _) in begin
    embNe (wkNe w n) ≡˘⟨ embNe-natural w n ⟩
    wkTm w (embNe n) ≈⟨ wkTm-pres-≈ w p ⟩
    wkTm w t ∎
  P-invar-⊆ (a ⇒ b) w {t = t} {x = x} p = λ w' u y q → P-invar-≈ b (cong-app1≈ (≡˘-to-≈ (wkTm-pres-∙ w w' t))) (p (w ∙ w') u y q)
  P-invar-⊆ (◻ a)   w {t = t} {x = x} _p = {!!}

  data Q : (Δ : Ctx) → {Γ : Ctx} → (σ : Sub Γ Δ) → (s : Ctx' Γ Δ) → Set where
    -- Q []       {_Γ} []             tt                   = ⊤
    []   : Q [] [] tt
    -- Q (Δ `, a) {Γ}  (σ `, t)       (elem (s , x))       = Q Δ σ s ∧ P a t x
    _`,_ : {s : Ctx' Γ Δ} → Q Δ σ s → {x : Ty' Γ a} → P a t x → Q (Δ `, a) (σ `, t) (elem (s , x))
    -- Q (Δ 🔒)    {Γ}  (lock {Β} {ΒR} σ e) (elem (Β' , (ΒR' , e') , s)) = ∃ λ Β'≡Β → ∃ λ ΒR'≡ΒR → subst₂ (CExt Γ) Β'≡Β ΒR'≡ΒR e' ≡ e ∧ Q Δ σ (subst (λ Γ → Ctx' Γ Δ) Β'≡Β s)
    _🔒   : {Β ΒR : Ctx} → {σ : Sub Β Δ} → {e : CExt Γ Β ΒR} → {s : Ctx' Β Δ} → Q Δ σ s → Q (Δ 🔒) (lock σ e) (elem (Β , (ΒR , e) , s))

  Q-invar-⊆ : ∀ (Δ : Ctx) (w : Γ ⊆ Γ') {σ : Sub Γ Δ} {s : Ctx' Γ Δ} (_q : Q Δ σ s) → Q Δ (wkSub w σ) (wkCtx' {Δ = Δ} w s)
  Q-invar-⊆ = {!!}

reflect : (a : Ty) → (n : Ne  Γ a) → Ty' Γ a
reify   : (a : Ty) → (x : Ty' Γ a) → Nf  Γ a

-- interpretation of neutrals
reflect 𝕓       n = n
reflect (a ⇒ b) n = record
  { fun     = λ w x → reflect b (app (wkNe w n) (reify a x))
  ; pres-≋  = {!!}
  ; natural = {!!}
  }
reflect (◻ a)   n = record
  { fun     = λ w (_ , e) → reflect a (unbox (wkNe w n) e)
  ; natural = {!!}
  }

-- reify values to normal forms
reify 𝕓       n = up𝕓 n
reify (a ⇒ b) f = lam (reify b (f .apply (fresh {a = a}) (reflect a var0)))
reify (◻ a)   g = box (reify a (g .apply idWk (-, new)))

reify-pres-≋ : ∀ (a : Ty) {x x' : Ty' Γ a} (x≋x' : x ≋[ evalTy a ] x') → reify a x ≡ reify a x'
reify-pres-≋ 𝕓       x≋x' = cong up𝕓 x≋x'
reify-pres-≋ (a ⇒ b) x≋x' = cong lam (reify-pres-≋ b (x≋x' .pw (fresh {a = a}) (reflect a var0)))
reify-pres-≋ (◻ a)   x≋x' = cong box (reify-pres-≋ a (x≋x' .pw idWk (-, new)))

reify-natural : ∀ (a : Ty) (x : Ty' Γ a) (w : Γ ⊆ Γ') → reify a (wk[ evalTy a ] w x) ≡ wkNf w (reify a x)
reify-natural 𝕓 x w = refl
reify-natural (a ⇒ b) x w = let open ≡-Reasoning in begin
  reify (a ⇒ b) (wk[ evalTy (a ⇒ b) ] w x)                                                                      ≡⟨⟩
  lam (reify b (x .apply (w ∙ fresh {a = a}) (reflect a var0)))                                                 ≡⟨ {!!} ⟩
  lam (reify b (x .apply (fresh {a = a} ∙ keep {a = a} w) (reflect a (wkNe (keep {a = a} w) var0))))            ≡⟨ {!!} ⟩
  lam (reify b (x .apply (fresh {a = a} ∙ keep {a = a} w) (wk[ evalTy a ] (keep {a = a} w) (reflect a var0))))  ≡⟨ {!!} ⟩
  lam (reify b (wk[ evalTy b ] (keep {a = a} w) (x .apply (fresh {a = a}) (reflect a var0))))                   ≡⟨ {!!} ⟩
  lam (wkNf (keep {a = a} w) (reify b (x .apply (fresh {a = a}) (reflect a var0))))                             ≡⟨⟩
  wkNf w (reify (a ⇒ b) x)                                                                                      ∎
reify-natural (◻ a) x w = {!!}

private
  reflect-pres-P : ∀ (a : Ty) (n : Ne Γ a) → P a (embNe n) (reflect a n)
  reify-pres-P   : ∀ (a : Ty) (t : Tm Γ a) (x : Ty' Γ a) (p : P a t x) → embNf (reify a x) ≈ t

  reflect-pres-P 𝕓       n = ≈-refl
  reflect-pres-P (a ⇒ b) n = λ w u x p → P-invar-≈ b (cong-app≈ (≡˘-to-≈ (embNe-natural w n)) (reify-pres-P a u x p)) (reflect-pres-P b (app (wkNe w n) (reify a x)))
  reflect-pres-P (◻ a)   n = λ w e → P-invar-≈ {!!} {!!} (reflect-pres-P a (unbox (wkNe w n) e))

  reify-pres-P 𝕓 _ _ p = p
  reify-pres-P (a ⇒ b) t x@(elem f _f-pres-≋ f-natural) p = let open EqReasoning (Tm-setoid _ (a ⇒ b)) in begin
    embNf (reify (a ⇒ b) x)                           ≡⟨⟩
    embNf (lam (reify b (f fresh (reflect a var0))))  ≡⟨⟩
    lam (embNf (reify b (f fresh (reflect a var0))))  ≈⟨ cong-lam≈ (reify-pres-P b (app (wkTm fresh t) var0) (f fresh (reflect a var0)) (p fresh _ _ (reflect-pres-P a var0))) ⟩
    lam (app (wkTm fresh t) var0)                     ≈˘⟨ exp-fun≈ t ⟩
    t ∎
  reify-pres-P (◻ a) t g p = let open EqReasoning (Tm-setoid _ (◻ a)) in begin
    embNf (reify (◻ a) g)                           ≡⟨⟩
    embNf (box (reify a (g .apply idWk (-, new))))  ≡⟨⟩
    box (embNf (reify a (g .apply idWk (-, new))))  ≈⟨ cong-box≈ (reify-pres-P a (unbox (wkTm idWk t) new) (g .apply idWk (-, new)) (p idWk new)) ⟩
    box (unbox (wkTm idWk t) new)                   ≈⟨ {!!} ⟩
    box (unbox t new)                               ≈˘⟨ exp-box≈ t ⟩
    t ∎

  evalAcc-P : ∀ (e : CExt Γ ΓL ΓR) (σ : Sub Δ Γ) (s : Ctx' Δ Γ) (q : Q Γ σ s) → Q (ΓL 🔒) (lock (factor2Sub e σ) (factor2Extₛ e σ)) (evalAcc e .apply s)
  evalAcc-P nil       σ s q = {!!}
  evalAcc-P (ext e)   σ s q = {!!}
  evalAcc-P (ext🔒- e) (lock {ΔL = .Β} σ e') (elem (Β , (ΒR , .e') , s)) (q 🔒) with evalAcc e .apply s | evalAcc-P e σ s q
  ... | x | (q' 🔒) = q' 🔒

  λ-P : ∀ {Γ : Ctx} {a : Ty} (t : Tm Γ (◻ a))
        (_ : ∀ {Δ : Ctx} (σ : Sub Δ Γ) (s : Ctx' Δ Γ) (q : Q Γ σ s) → P (◻ a) (substTm σ t) (evalTm t .apply s))
      → ∀ {Δ : Ctx} (σ : Sub Δ (Γ 🔒)) (s : Ctx' Δ (Γ 🔒)) (q : Q (Γ 🔒) σ s) → P a (unbox (substTm (factor2Sub new σ) t) (factor2Extₛ new σ)) (λ' (evalTm t) .apply s)
  λ-P t p (lock σ e) (elem (Β , (_ , e) , s)) (q 🔒) = {!P-invar-≈˘ _ (cong-unbox≈ ≈-refl []-unit-left nil-unit-left) (p σ s q idWk e)!}

  evalTm-P : ∀ (t : Tm Γ a) (σ : Sub Δ Γ) (s : Ctx' Δ Γ) (q : Q Γ σ s) → P a (substTm σ t) (evalTm t .apply s)
  evalTm-P     (var v)             σ s q = {!!}
  evalTm-P {Γ} (lam {b = b} t)     σ s q = λ w u x p → P-invar-≈˘ b (≈-trans (red-fun≈ (wkTm (keep w) (substTm (keepₛ σ) t)) u) {!!}) (evalTm-P t (wkSub w σ `, u) (elem (wk[ evalCtx Γ ] w s , x)) (Q-invar-⊆ Γ w q `, p))
  evalTm-P     (app {b = b} t u)   σ s q = P-invar-≈ b (cong-app1≈ (≡-to-≈ (wkTm-pres-id (substTm σ t)))) (evalTm-P t σ s q idWk (substTm σ u) (evalTm u .apply s) (evalTm-P u σ s q))
  evalTm-P {Γ} (box {a = a} t)     σ s q = λ w e → P-invar-≈˘ a {!!} (evalTm-P t (lock (wkSub w σ) e) (elem (-, (-, e) , wk[ evalCtx Γ ] w s)) (Q-invar-⊆ Γ w q 🔒))
  evalTm-P     (unbox {a = a} t e) σ s q = P-invar-≈ a obs (λ-P t (evalTm-P t) (lock (factor2Sub e σ) (factor2Extₛ e σ)) (evalAcc e .apply s) (evalAcc-P e σ s q) )
    where
      postulate obs : substTm (lock (factor2Sub e σ) (factor2Extₛ e σ)) (unbox t new) ≈ substTm σ (unbox t e)

-- (reflected) identity substitution (one direction of the prinicipal lemma?)
idₛ' : (Γ : Ctx) → Ctx' Γ Γ
idₛ' []       = tt
idₛ' (Γ `, a) = record { elem = (wkCtx' {Δ = Γ} (fresh {a = a}) (idₛ' Γ) , reflect a var0) }
idₛ' (Γ 🔒)    = elem (-, (-, new) , idₛ' Γ)
