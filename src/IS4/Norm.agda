module IS4.Norm where

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)

open import Function

open import IS4.Term

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var   : Var Γ a → Ne Γ a
  app   : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
  unbox : Ne ΓL (◻ a) → CExt Γ ΓL ΓR → Ne Γ a

pattern var0 = var v0
pattern var1 = var v1
pattern var2 = var v2

data Nf where
  up𝕓 : Ne Γ 𝕓 → Nf Γ 𝕓
  lam : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  box : Nf (Γ 🔒) a → Nf Γ (◻ a)

pattern var0 = up𝕓 (var v0)
pattern var1 = up𝕓 (var v1)
pattern var2 = up𝕓 (var v2)

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

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

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
  lock : A ΓL → CExt Γ ΓL ΓR  → Lock A Γ

-- interpretation of types
Tm' : Ctx → Ty → Set
Tm' Γ  𝕓       = Nf Γ 𝕓
Tm' Γ  (a ⇒ b) = {Γ' : Ctx} → Γ ⊆ Γ' → (Tm' Γ' a → Tm' Γ' b)
Tm' ΓL (◻ a)  = {Γ ΓR : Ctx} → CExt Γ ΓL ΓR → Tm' Γ a

-- interpretation of contexts
Sub' : Ctx → Ctx → Set
Sub' Δ []       = ⊤
Sub' Δ (Γ `, a) = Sub' Δ Γ × Tm' Δ a
Sub' Δ (Γ 🔒)    = Lock (λ Γ' → Sub' Γ' Γ) Δ

-- values in the model can be weakened
wkTm' : Γ ⊆ Γ' → Tm' Γ a → Tm' Γ' a
wkTm' {a = 𝕓}     w n  = wkNf w n
wkTm' {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTm' {a = ◻ a}  w bx = λ e → wkTm' (factor1≤ e w) (bx (factor1Ext e w))

-- substitutions in the model can be weakened
wkSub' : Γ ⊆ Γ' → Sub' Γ Δ → Sub' Γ' Δ
wkSub' {Δ = []}     w tt          = tt
wkSub' {Δ = Δ `, a} w (s , x)     = wkSub' w s , wkTm' w x
wkSub' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSub' (factor2≤ e w) s) (factor2Ext e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Tm' ΓL (◻ a) → CExt Γ ΓL ΓR → Tm' Γ a
unbox' bx e = bx e

unlock' : Sub' Δ (Γ 🔒) → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → Sub' ΔL Γ × CExt Δ ΔL ΔR }
unlock' (lock γ e) = _ , γ , e

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
reify {a = 𝕓}     x  = x
reify {a = a ⇒ b} x  = lam (reify (x (drop idWk) (reflect (var ze))))
reify {a = ◻ a}  bx = box (reify (bx new))

-- identity substitution
idₛ' : Sub' Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, x} = wkSub' (drop idWk) idₛ' , reflect (var ze)
idₛ' {Γ 🔒}    = lock (idₛ' {Γ}) new

-- interpretation of variables
substVar' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

CExt' : CExt Γ ΓL ΓR → Sub'- Γ →̇ Sub'- (ΓL 🔒)
CExt' nil       γ           = lock γ nil                                                              -- = η            ("return")
CExt' (ext e)   (γ , _)     = CExt' e γ                                                               -- = CExt' e ∘ π₁
CExt' (ext🔒- e) (lock γ e') = let (_ , γ' , e'') = unlock' (CExt' e γ) in lock γ' (extRAssoc e'' e') -- = ^(CExt' e)   ("bind")

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval (var x)     s = substVar' x s
eval (lam t)     s = λ e x → eval t (wkSub' e s , x)
eval (app t u)   s = (eval t s) idWk (eval u s)
eval (box t)     s = λ e → eval t (lock s e)
eval (unbox t e) s = let (_ , s' , e') = unlock' (CExt' e s) in unbox' (eval t s') e' -- = ^(eval t) ∘ CExt' e

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
  lock : Nfₛ ΔL Γ → CExt Δ ΔL ΔR → Nfₛ Δ (Γ 🔒)

-- embeddding of substitution normal forms back into substitutions
embNfₛ : Nfₛ Γ Δ → Sub Γ Δ
embNfₛ []         = []
embNfₛ (n `, s)   = embNfₛ n `, embNf s
embNfₛ (lock n s) = lock (embNfₛ n) s

Nfₛ- : Ctx → Ctx → Set
Nfₛ- Δ Γ = Nfₛ Γ Δ

-- interpretation of substitutions
evalₛ : Sub Γ Δ → Sub'- Γ  →̇ Sub'- Δ
evalₛ []         γ = tt
evalₛ (s `, t)   γ = evalₛ s γ , eval t γ
evalₛ (lock s e) γ = let (_ , γ' , e') = unlock' (CExt' e γ) in lock (evalₛ s γ') e' -- = Lock (evalₛ s ∘ CExt' e)

-- retraction of evalₛ
quotₛ : Sub'- Γ →̇ Nfₛ- Γ
quotₛ {[]}     tt         = []
quotₛ {Γ `, _} (s , x)    = (quotₛ s) `, (reify x)
quotₛ {Γ 🔒}    (lock s e) = lock (quotₛ s) e

-- normalization function, for substitutions
normₛ : Sub Δ Γ → Nfₛ Δ Γ
normₛ s = quotₛ (evalₛ s idₛ')
