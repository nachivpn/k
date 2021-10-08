module IS4.Applications.Staged where

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_; proj₁; proj₂; ∃)

open import IS4.Term.Base

---------------
-- Normal forms
---------------

data Ne : Ctx → Ty → Set
data Nf : Ctx → Ty → Set

data Ne where
  var   : Var Γ a → Ne Γ a
  app   : Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
  unbox : Ne ΓL (◻ a) → CExt Γ ΓL ΓR → Ne Γ a

data Nf where
  up𝕓 : Ne Γ 𝕓 → Nf Γ 𝕓
  lam : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  box : Tm (Γ 🔒) a → Nf Γ (◻ a)

-- embedding into terms

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var x)     = var x
embNe (app m n)   = app (embNe m) (embNf n)
embNe (unbox n x) = unbox (embNe n) x

embNf (up𝕓 x) = embNe x
embNf (lam n) = lam (embNf n)
embNf (box n) = box n

-- normal forms of substitutions
data Nfₛ : Ctx → Ctx → Set where
  []   : Nfₛ Γ []
  _`,_ : Nfₛ Γ Δ → Nf Γ a → Nfₛ Γ (Δ `, a)
  lock : Nfₛ ΔL Γ → CExt Δ ΔL ΔR → Nfₛ Δ (Γ 🔒)

-- embedding of substitution normal forms back into substitutions
embNfₛ : Nfₛ Γ Δ → Sub Γ Δ
embNfₛ []         = []
embNfₛ (n `, s)   = embNfₛ n `, embNf s
embNfₛ (lock n s) = lock (embNfₛ n) s

Nfₛ- : Ctx → Ctx → Set
Nfₛ- Δ Γ = Nfₛ Γ Δ

-- weakening lemmas

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var x)      = var (wkVar w x)
wkNe w (app m n)    = app (wkNe w m) (wkNf w n)
wkNe w (unbox n e)  = unbox (wkNe (factor2≤ e w) n) (factor2Ext e w)

wkNf e (up𝕓 x) = up𝕓 (wkNe e x)
wkNf e (lam n) = lam (wkNf (keep e) n)
wkNf e (box n) = box (wkTm (keep🔒 e) n)

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
Tm' ΓL (◻ a)  = {Γ ΓR : Ctx} → CExt Γ ΓL ΓR → Tm' Γ a × Tm Γ a

-- interpretation of contexts
Sub' : Ctx → Ctx → Set
Sub' Δ []       = ⊤
Sub' Δ (Γ `, a) = Sub' Δ Γ × Tm' Δ a
Sub' Δ (Γ 🔒)    = Lock (λ Γ' → Sub' Γ' Γ) Δ

-- values in the model can be weakened
wkTm' : Γ ⊆ Γ' → Tm' Γ a → Tm' Γ' a
wkTm' {a = 𝕓}     w n  = wkNf w n
wkTm' {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTm' {a = ◻ a}  w bx = λ e → let b = bx (factor1Ext e w)
                                in wkTm' (factor1≤ e w) (proj₁ b) , wkTm (factor1≤ e w) (proj₂ b)

-- substitutions in the model can be weakened
wkSub' : Γ ⊆ Γ' → Sub' Γ Δ → Sub' Γ' Δ
wkSub' {Δ = []}     w tt          = tt
wkSub' {Δ = Δ `, a} w (s , x)     = wkSub' w s , wkTm' w x
wkSub' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSub' (factor2≤ e w) s) (factor2Ext e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Tm' ΓL (◻ a) → CExt Γ ΓL ΓR → Tm' Γ a
unbox' bx e = proj₁ (bx e)

-------------------------
-- Normalization
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
reflect {a = ◻ a} n  = λ e → (reflect (unbox n e)) , (unbox (embNe n) e)

-- reify values to normal forms
reify {a = 𝕓}     x = x
reify {a = a ⇒ b} x = lam (reify (x (drop idWk) (reflect (var ze))))
reify {a = ◻ a}  bx = box (proj₂ (bx (ext🔒- nil)))

-- identity substitution
idₛ' : Sub' Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, x} = wkSub' (drop idWk) idₛ' , reflect (var ze)
idₛ' {Γ 🔒}    = lock (idₛ' {Γ}) (ext🔒- nil)

-- interpretation of variables
substVar' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

-- retraction of interpretation
quot : (Sub'- Γ →̇ Tm'- a) → Nf Γ a
quot f = reify (f idₛ')

-- retraction of interpretation
quotₛ : Sub'- Γ →̇ Nfₛ- Γ
quotₛ {[]}     tt         = []
quotₛ {Γ `, _} (s , x)    = (quotₛ s) `, (reify x)
quotₛ {Γ 🔒}    (lock s e) = lock (quotₛ s) e

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval (var x)                     s
  = substVar' x s
eval (lam t)                     s
  = λ e x → eval t (wkSub' e s , x)
eval (app t u)                   s
  = (eval t s) idWk (eval u s)
eval (box t)                     s
  = λ e → (eval t (lock s e)) , substTm (embNfₛ (quotₛ (lock s e))) t
eval (unbox t nil)               s
  = unbox' (eval t s) nil
eval (unbox t (ext e))           (s , _)
  = eval (unbox t e) s
eval (unbox t (ext🔒- e))         (lock s nil)
  = eval (unbox t e) s
eval (unbox t (ext🔒- e))         (lock s (ext e'))
  = wkTm' fresh (eval (unbox t (ext🔒- e)) (lock s e'))
eval (unbox t (ext🔒- nil))       (lock s (ext🔒- e'))
  = unbox' (eval t s) (ext🔒- e')
eval (unbox t (ext🔒- (ext e)))   (lock (s , _) (ext🔒- e'))
  = eval (unbox t (ext🔒- e)) (lock s (ext🔒- e'))
eval (unbox t (ext🔒- (ext🔒- e))) (lock (lock s e'') (ext🔒- e'))
  = eval (unbox t (ext🔒- e)) (lock s (ext🔒- (extRAssoc e'' e')))

-- interpretation of substitutions
evalₛ : Sub Γ Δ → Sub'- Γ  →̇ Sub'- Δ
evalₛ []                         s'
  = tt
evalₛ (s `, t)                   s'
  = (evalₛ s s') , eval t s'
evalₛ (lock s nil)               s'
  = lock (evalₛ s s') nil
evalₛ (lock s (ext e))           (s' , _)
  = evalₛ (lock s e) s'
evalₛ (lock s (ext🔒- nil))       (lock s' e')
  = lock (evalₛ s s') e'
evalₛ (lock s (ext🔒- (ext e)))   (lock (s' , _) e')
  = evalₛ (lock s (ext🔒- e)) (lock s' e')
evalₛ (lock s (ext🔒- (ext🔒- e))) (lock (lock s' e'') e')
  = evalₛ (lock s (ext🔒- e)) (lock s' (extRAssoc e'' e'))

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (eval t)

-- normalization function, for substitutions
normₛ : Sub Δ Γ → Nfₛ Δ Γ
normₛ s = quotₛ (evalₛ s idₛ')

-- Example
module _ where
  open import Relation.Binary.PropositionalEquality

  -- Eliminability theorem
  eliminability : (t : Tm Γ (◻ a)) → ∃ λ u → norm t ≡ box u
  eliminability t = _ , refl
