module IS4.Norm where

open import Data.Unit    using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_)

open import IS4.Term

------------
-- NbE Model
------------

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

-- semantic counterpart of `lock` from `Sub`
data Lock (A : Ctx → Set) : Ctx → Set where
  lock : A ΔL → CExt Γ ΔL ΔR  → Lock A Γ

-- interpretation of types
Tm' : Ctx → Ty → Set
Tm' Γ  𝕓       = Nf Γ 𝕓
Tm' Γ  (a ⇒ b) = {Γ' : Ctx} → Γ ⊆ Γ' → (Tm' Γ' a → Tm' Γ' b)
Tm' ΓL (◻ a)  = {ΓL' Γ ΓR : Ctx} → ΓL ⊆ ΓL' → CExt Γ ΓL' ΓR → Tm' Γ a

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
wkTm' {a = 𝕓}     w n  = wkNf w n
wkTm' {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTm' {a = ◻ a}  w bx = λ w' e → bx (w ∙ w') e

-- substitutions in the model can be weakened
wkSub' : Γ ⊆ Γ' → Sub' Γ Δ → Sub' Γ' Δ
wkSub' {Δ = []}     w tt          = tt
wkSub' {Δ = Δ `, a} w (s , x)     = wkSub' w s , wkTm' w x
wkSub' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSub' (factorWk e w) s) (factorExt e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Tm' ΓL (◻ a) → CExt Γ ΓL ΓR → Tm' Γ a
unbox' bx e = bx idWk e

unlock' : Sub' Δ (Γ 🔒) → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → Sub' ΔL Γ × CExt Δ ΔL ΔR }
unlock' (lock γ e) = _ , γ , e

-- interpretation of variables
substVar' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

CExt' : CExt Γ ΓL ΓR → Sub'- Γ →̇ Sub'- (ΓL 🔒)
CExt' nil       γ           = lock γ nil                                                             -- = η            ("return")
CExt' (ext e)   (γ , _)     = CExt' e γ                                                              -- = CExt' e ∘ π₁
CExt' (ext🔒- e) (lock γ e') = let (_ , γ' , e'') = unlock' (CExt' e γ) in lock γ' (extRAssoc e'' e') -- = ^(CExt' e)   ("bind")

-- "Left" context of factoring with a substitution (see factorExtₛ)
lCtxₛ' : (e : CExt Γ ΓL ΓR) (s : Sub' Δ Γ) → Ctx
lCtxₛ' {Γ = Γ} {Δ = Δ} nil   s          = Δ
lCtxₛ' {Γ = Γ `, a} (ext e)  (s , t)     = lCtxₛ' {Γ = Γ} e s
lCtxₛ' (ext🔒- e)             (lock s e') = lCtxₛ' e s

-- "Right" context of factoring with a substitution (see factorExtₛ)
rCtxₛ' : (e : CExt Γ ΓL ΓR) (s : Sub' Δ Γ) → Ctx
rCtxₛ' nil       s                     = []
rCtxₛ' (ext e)   (s , t)               = rCtxₛ' e s
rCtxₛ' (ext🔒- e) (lock {ΔR = ΔR} s e') = rCtxₛ' e s ,, ΔR

-- same as factor2Extₛ
factorExtₛ' : (e : CExt Γ ΓL ΓR) (s : Sub' Δ Γ) → CExt Δ (lCtxₛ' e s) (rCtxₛ' e s)
factorExtₛ' nil       s           = nil
factorExtₛ' (ext e)   (s , _)     = factorExtₛ' e s
factorExtₛ' (ext🔒- e) (lock s e') = extRAssoc (factorExtₛ' e s) e'

-- same as factor2Subₛ
factorSubₛ' : (e : CExt Γ ΓL ΓR) (s : Sub' Δ Γ) → Sub' (lCtxₛ' e s) ΓL
factorSubₛ' nil       s           = s
factorSubₛ' (ext e)   (s , t)     = factorSubₛ' e s
factorSubₛ' (ext🔒- e) (lock s e') = factorSubₛ' e s

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval (var x)     s = substVar' x s
eval (lam t)     s = λ w x → eval t (wkSub' w s , x)
eval (app t u)   s = (eval t s) idWk (eval u s)
eval (box t)     s = λ w e → eval t (lock (wkSub' w s) e)
eval (unbox t e) s = unbox' (eval t (factorSubₛ' e s)) (factorExtₛ' e s)

-- interpretation of substitutions (simply "do everything pointwise")
evalₛ : Sub Γ Δ → Sub'- Γ  →̇ Sub'- Δ
evalₛ []         γ = tt
evalₛ (s `, t)   γ = evalₛ s γ , eval t γ
evalₛ (lock s e) γ = let (_ , γ' , e') = unlock' (CExt' e γ) in lock (evalₛ s γ') e' -- = Lock (evalₛ s ∘ CExt' e)

-------------------------
-- Normalization function
-------------------------

reify   : Tm' Γ a → Nf Γ a
reflect : Ne Γ a  → Tm' Γ a

-- interpretation of neutrals
reflect {a = 𝕓} n     = up𝕓 n
reflect {a = a ⇒ b} n = λ w x → reflect (app (wkNe w n) (reify x))
reflect {a = ◻ a} n  = λ w e → reflect (unbox (wkNe w n) e)

-- reify values to normal forms
reify {a = 𝕓}     x  = x
reify {a = a ⇒ b} x  = lam (reify (x (drop idWk) (reflect (var ze))))
reify {a = ◻ a}  bx = box (reify (bx idWk new))

-- identity substitution
idₛ' : Sub' Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, x} = wkSub' (drop idWk) idₛ' , reflect (var ze)
idₛ' {Γ 🔒}    = lock (idₛ' {Γ}) new

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

-- retraction of evalₛ
quotₛ : Sub'- Γ →̇ Nfₛ- Γ
quotₛ {[]}     tt         = []
quotₛ {Γ `, _} (s , x)    = (quotₛ s) `, (reify x)
quotₛ {Γ 🔒}    (lock s e) = lock (quotₛ s) e

-- normalization function, for substitutions
normₛ : Sub Δ Γ → Nfₛ Δ Γ
normₛ s = quotₛ (evalₛ s idₛ')
