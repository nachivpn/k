{-# OPTIONS --safe --without-K #-}
module IK.Norm.NbE.Model where

open import Data.Unit    using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_)

open import IK.Term

------------
-- NbE Model
------------

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

-- semantic counterpart of `box` from `Tm`
data Box (A : Ctx → Set) : Ctx → Set where
  box : A (Γ 🔒) → Box A Γ

-- semantic counterpart of `lock` from `Sub`
data Lock (A : Ctx → Set) : Ctx → Set where
  lock : A ΓL → LFExt Γ (ΓL 🔒) ΓR  → Lock A Γ
  -- equivalently, `lock : 🔒-free Γ' → A Γ → Lock A (Γ 🔒 ,, Γ')`

-- interpretation of types

Tm' : Ctx → Ty → Set
Tm' Γ 𝕓       = Nf Γ 𝕓
Tm' Γ (a ⇒ b) = {Γ' : Ctx} → Γ ⊆ Γ' → (Tm' Γ' a → Tm' Γ' b)
Tm' Γ (□ a)   = Box (λ Γ' → Tm' Γ' a) Γ

Tm'- : Ty → Ctx → Set
Tm'- a Γ = Tm' Γ a

-- interpretation of contexts
Sub' : Ctx → Ctx → Set
Sub' Δ []       = ⊤
Sub' Δ (Γ `, a) = Sub' Δ Γ × Tm' Δ a
Sub' Δ (Γ 🔒)    = Lock (λ Γ' → Sub' Γ' Γ) Δ

Sub'- : Ctx → Ctx → Set
Sub'- Δ Γ = Sub' Γ Δ

-- values in the model can be weakened
wkTm' : Γ ⊆ Γ' → Tm' Γ a → Tm' Γ' a
wkTm' {a = 𝕓}     e n       = wkNf e n
wkTm' {a = a ⇒ b} e f       = λ e' y → f (e ∙ e') y
wkTm' {a = □ a}   e (box x) = box (wkTm' (keep🔒 e) x)

-- substitutions in the model can be weakened
wkSub' : Γ ⊆ Γ' → Sub' Γ Δ → Sub' Γ' Δ
wkSub' {Δ = []}     w tt          = tt
wkSub' {Δ = Δ `, a} w (s , x)     = wkSub' w s , wkTm' w x
wkSub' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSub' (sliceLeft e w) s) (wkLFExt e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Box (λ Δ → Tm' Δ a) ΓL → LFExt Γ (ΓL 🔒) ΓR → Tm' Γ a
unbox' (box x) e = wkTm' (LFExtToWk e) x

unlock' : Sub' Δ (Γ 🔒) → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → Sub' ΔL Γ × LFExt Δ (ΔL 🔒) ΔR }
unlock' (lock γ e) = _ , γ , e

-- interpretation of variables
substVar' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

LFExt' : LFExt Γ (ΓL 🔒) ΓR → Sub'- Γ →̇ Sub'- (ΓL 🔒)
LFExt' nil     γ       = γ          -- = id
LFExt' (ext e) (γ , _) = LFExt' e γ -- = LFExt' e ∘ π₁

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval (var x)     s = substVar' x s
eval (lam t)     s = λ e x → eval t (wkSub' e s , x)
eval (app t u)   s = (eval t s) idWk (eval u s)
eval (box t)     s = box (eval t (lock s nil))
eval (unbox t e) s = let (_ , s' , e') = unlock' (LFExt' e s) in unbox' (eval t s') e' -- = ^(eval t) ∘ LFExt' e

-- interpretation of substitutions (simply "do everything pointwise")
evalₛ : Sub Γ Δ → Sub'- Γ  →̇ Sub'- Δ
evalₛ []         γ = tt
evalₛ (s `, t)   γ = evalₛ s γ , eval t γ
evalₛ (lock s e) γ = let (_ , γ' , e') = unlock' (LFExt' e γ) in lock (evalₛ s γ') e' -- = Lock (evalₛ s ∘ LFExt' e)
