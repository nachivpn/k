module IS4.Norm where

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)

open import IS4.Term

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var   : Var Γ a → Ne Γ a
  app   : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
  unbox : Ne ΓL (◻ a) → Ext tt Γ ΓL ΓR → Ne Γ a

data Nf where
  up𝕓 : Ne Γ 𝕓 → Nf Γ 𝕓
  lam : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  box : Nf (Γ 🔒) a → Nf Γ (◻ a)

-- embedding into terms

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var x)     = var x
embNe (app m n)   = app (embNe m) (embNf n)
embNe (unbox n x) = unbox (embNe n) x

embNf (up𝕓 x) = embNe x
embNf (lam n) = lam (embNf n)
embNf (box n) = box (embNf n)

-- weakening lemmas

wkNe : Γ' ≤ Γ → Ne Γ a → Ne Γ' a
wkNf : Γ' ≤ Γ → Nf Γ a → Nf Γ' a

wkNe w (var x)      = var (wkVar w x)
wkNe w (app m n)    = app (wkNe w m) (wkNf w n)
wkNe w (unbox n e)  = unbox (wkNe (factor2≤ e w) n) (factor2Ext e w)

wkNf e (up𝕓 x) = up𝕓 (wkNe e x)
wkNf e (lam n) = lam (wkNf (keep e) n)
wkNf e (box n) = box (wkNf (keep🔒 e) n)

------------
-- NbE Model
------------

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

-- semantic counterpart of `lock` from `Sub`
data Lock (A : Ctx → Set) : Ctx → Set where
  lock : A ΓL → Ext tt Γ ΓL ΓR  → Lock A Γ

-- interpretation of types

Tm' : Ctx → Ty → Set
Tm' Γ  𝕓       = Nf Γ 𝕓
Tm' Γ  (a ⇒ b) = {Γ' : Ctx} → Γ' ≤ Γ → (Tm' Γ' a → Tm' Γ' b)
Tm' ΓL (◻ a)  = {Γ ΓR : Ctx} → Ext tt Γ ΓL ΓR → Tm' Γ a

-- interpretation of contexts
Sub' : Ctx → Ctx → Set
Sub' Δ []       = ⊤
Sub' Δ (Γ `, a) = Sub' Δ Γ × Tm' Δ a
Sub' Δ (Γ 🔒)    = Lock (λ Γ' → Sub' Γ' Γ) Δ

-- values in the model can be weakened
wkTm' : Γ' ≤ Γ → Tm' Γ a → Tm' Γ' a
wkTm' {a = 𝕓}     w n  = wkNf w n
wkTm' {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTm' {a = ◻ a}  w bx = λ e → wkTm' (factor1≤ e w) (bx (factor1Ext e w))

-- substitutions in the model can be weakened
wkSub' : Γ' ≤ Γ → Sub' Γ Δ → Sub' Γ' Δ
wkSub' {Δ = []}     w tt          = tt
wkSub' {Δ = Δ `, a} w (s , x)     = wkSub' w s , wkTm' w x
wkSub' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSub' (factor2≤ e w) s) (factor2Ext e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Tm' ΓL (◻ a) → Ext tt Γ ΓL ΓR → Tm' Γ a
unbox' bx e = bx e

-------------------------
-- Normalization function
-------------------------

Sub- : Ctx → Ctx → Set
Sub- Δ Γ = Sub Γ Δ

Sub'- : Ctx → Ctx → Set
Sub'- Δ Γ = Sub' Γ Δ

Tm'- : Ty → Ctx → Set
Tm'- a Γ = Tm' Γ a

reify   : Tm' Γ a → Nf Γ a
reflect : Ne Γ a  → Tm' Γ a

-- interpretation of neutrals
reflect {a = 𝕓} n     = up𝕓 n
reflect {a = a ⇒ b} n = λ e x → reflect (app (wkNe e n) (reify x))
reflect {a = ◻ a} n  = λ e → reflect (unbox n e)

-- reify values to normal forms
reify {a = 𝕓}     x   = x
reify {a = a ⇒ b} x   = lam (reify (x (drop idWk) (reflect (var ze))))
reify {a = ◻ a}  bx  = box (reify (bx (ext🔒 _ nil)))

-- identity substitution
idₛ' : Sub' Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, x} = wkSub' (drop idWk) idₛ' , reflect (var ze)
idₛ' {Γ 🔒}    = lock (idₛ' {Γ}) (ext🔒 _ nil)

-- interpretation of variables
substVar' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

import Context as C
import IS4.Substitution as S

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval (var x)              s
  = substVar' x s
eval (lam t)              s
  = λ e x → eval t (wkSub' e s , x)
eval (app t u)            s
  = (eval t s) idWk (eval u s)
eval (box t)              s
  = λ e → eval t (lock s e)
eval (unbox t nil)        s
  = unbox' (eval t s) nil
eval (unbox t (ext e))    (s , _)
  = eval (unbox t e) s
eval (unbox t (C.ext🔒 f e)) (lock s C.nil)
  = eval (unbox t e) s
eval (unbox t (C.ext🔒 f e)) (lock s (C.ext e'))
  = wkTm' fresh (eval (unbox t (ext🔒 _ e)) (lock s e'))
eval (unbox t (C.ext🔒 f C.nil)) (lock s (C.ext🔒 x e'))
  = unbox' (eval t s) (ext🔒 tt e')
eval (unbox t (C.ext🔒 f (C.ext e))) (lock (s , _) (C.ext🔒 x e'))
  = eval (unbox t (ext🔒 tt e)) (lock s (ext🔒 f e'))
eval (unbox t (ext🔒 f (C.ext🔒 _ e))) (lock (lock s e'') (C.ext🔒 _ e'))
  = eval (unbox t (ext🔒 _ e)) (lock s (ext🔒 _ (extRAssoc e'' e')))

-- retraction of interpretation
quot : (Sub'- Γ →̇ Tm'- a) → Nf Γ a
quot f = reify (f idₛ')

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (eval t)

----------------------------------
-- Normalization for substitutions
----------------------------------

-- (simply "do everything pointwise")

-- normal forms of substitutions
data Nfₛ : Ctx → Ctx → Set where
  []   : Nfₛ Γ []
  _`,_ : Nfₛ Γ Δ → Nf Γ a → Nfₛ Γ (Δ `, a)
  lock : Nfₛ ΔL Γ → Ext tt Δ ΔL ΔR → Nfₛ Δ (Γ 🔒)

-- embeddding of substitution normal forms back into substitutions
embNfₛ : Nfₛ Γ Δ → Sub Γ Δ
embNfₛ []         = []
embNfₛ (n `, s)   = embNfₛ n `, embNf s
embNfₛ (lock n s) = lock (embNfₛ n) s

Nfₛ- : Ctx → Ctx → Set
Nfₛ- Δ Γ = Nfₛ Γ Δ

-- interpretation of substitutions
evalₛ : Sub Γ Δ → Sub'- Γ  →̇ Sub'- Δ
evalₛ []                                 s'
  = tt
evalₛ (s `, t)                           s'
  = (evalₛ s s') , eval t s'
evalₛ (lock s nil)                       s'
  = lock (evalₛ s s') nil
evalₛ (lock s (ext e))                   (s' , _)
  = evalₛ (lock s e) s'
evalₛ (S.lock s (C.ext🔒 f C.nil))        (lock s' e')
  = lock (evalₛ s s') e'
evalₛ (S.lock s (C.ext🔒 f (C.ext e)))    (lock (s' , _) e')
  = evalₛ (lock s (ext🔒 tt e)) (lock s' e')
evalₛ (S.lock s (C.ext🔒 f (C.ext🔒 x e))) (lock (lock s' e'') e')
  = evalₛ (lock s (ext🔒 tt e)) (lock s' (extRAssoc e'' e'))

-- retraction of evalₛ
quotₛ : Sub'- Γ →̇ Nfₛ- Γ
quotₛ {[]}     tt         = []
quotₛ {Γ `, _} (s , x)    = (quotₛ s) `, (reify x)
quotₛ {Γ 🔒}    (lock s e) = lock (quotₛ s) e

-- normalization function, for substitutions
normₛ : Sub Δ Γ → Nfₛ Δ Γ
normₛ s = quotₛ (evalₛ s idₛ')
