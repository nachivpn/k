module IS4.Applications.IS4Plus where
-- IS4 with extensions

data Ty : Set where
  Unit : Ty
  𝕔    : Ty
  _⇒_ : Ty → Ty → Ty
  ◻_  : Ty → Ty
  Bool : Ty

variable
    a b c d : Ty

open import Context (Ty) hiding (ext🔒) public

------------------------------------
-- Variables, terms and substituions
------------------------------------

data Tm : Ctx → Ty → Set where

  var  : Var Γ a
       ---------
       → Tm Γ a

  lam  : Tm (Γ `, a) b
         -------------
       → Tm Γ (a ⇒ b)

  app  : Tm Γ (a ⇒ b) → Tm Γ a
         ---------------------
       → Tm Γ b

  box   : Tm (Γ 🔒) a
        ------------
        → Tm Γ (◻ a)

  unbox : Tm ΓL (◻ a) → CExt Γ ΓL ΓR
        ----------------------------
        → Tm Γ a

  unit : Tm Γ Unit

  true  : Tm Γ Bool

  false : Tm Γ Bool

  ifte  : CExt Γ ΓL ΓR → Tm ΓL Bool → Tm Γ a → Tm Γ a → Tm Γ a

TM : Ty → Ctx → Set
TM a Γ = Tm Γ a

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)     = var (wkVar w x)
wkTm w (lam t)     = lam (wkTm (keep w) t)
wkTm w (app t u)   = app (wkTm w t) (wkTm w u)
wkTm w (box t)     = box (wkTm (keep🔒 w) t)
wkTm w (unbox t e) = unbox (wkTm (factor2≤ e w) t) (factor2Ext e w)
wkTm w unit = unit
wkTm w true = true
wkTm w false = false
wkTm w (ifte e t t₁ t₂) = ifte (factor2Ext e w) (wkTm (factor2≤ e w) t) (wkTm w t₁) (wkTm w t₂)

open import IS4.Substitution Ty Tm var wkTm public

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_ ) renaming (proj₂ to snd)

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
  up𝕔 : Ne Γ 𝕔 → Nf Γ 𝕔
  lam : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  box : Nf (Γ 🔒) a → Nf Γ (◻ a)
  true : Nf Γ Bool
  false : Nf Γ Bool
  ifte : CExt Γ ΓL ΓR → Ne ΓL Bool → Nf Γ a → Nf Γ a → Nf Γ a
  unit : Nf Γ Unit

-- embedding into terms

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var x)     = var x
embNe (app m n)   = app (embNe m) (embNf n)
embNe (unbox n x) = unbox (embNe n) x

embNf (up𝕔 x) = embNe x
embNf (lam n) = lam (embNf n)
embNf (box n) = box (embNf n)
embNf true = true
embNf false = false
embNf (ifte x x₁ n n₁) = ifte x true (embNf n) (embNf n₁)
embNf unit = unit

-- weakening lemmas

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var x)      = var (wkVar w x)
wkNe w (app m n)    = app (wkNe w m) (wkNf w n)
wkNe w (unbox n e)  = unbox (wkNe (factor2≤ e w) n) (factor2Ext e w)

wkNf w (up𝕔 x) = up𝕔 (wkNe w x)
wkNf w (lam n) = lam (wkNf (keep w) n)
wkNf w (box n) = box (wkNf (keep🔒 w) n)
wkNf w true = true
wkNf w false = false
wkNf w (ifte e m n n₁) = ifte (factor2Ext e w) (wkNe (factor2≤ e w) m) (wkNf w n) (wkNf w n₁)
wkNf w unit = unit

NF NE : Ty → Ctx → Set
NF a Γ = Nf Γ a
NE a Γ = Ne Γ a

------------
-- NbE Model
------------

variable
  A B C : Ctx → Set

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

infixr 10 _→̇_

-- constructions on context-indexed families of sets
_⇒'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_⇒'_ A B Γ = {Γ' : Ctx} → Γ ⊆ Γ' → A Γ' → B Γ'

_×'_ : (Ctx → Set) → (Ctx → Set) → (Ctx → Set)
_×'_ A B Γ = A Γ × B Γ

Box : (Ctx → Set) → (Ctx → Set)
Box A ΓL = {Γ ΓR : Ctx} → CExt Γ ΓL ΓR → A Γ

-- semantic counterpart of `lock` from `Sub`
data Lock (A : Ctx → Set) : Ctx → Set where
  lock : A ΓL → CExt Γ ΓL ΓR  → Lock A Γ

⊤' : (Ctx → Set)
⊤' = λ Γ → ⊤

data Cov (A : Ctx → Set) : Ctx → Set where
  ret    : A Γ → Cov A Γ
  ifte'  : CExt Γ ΓL ΓR → NE Bool ΓL → Cov A Γ → Cov A Γ → Cov A Γ

wkCov : (Γ ⊆ Γ' → A Γ → A Γ') → Γ ⊆ Γ' → Cov A Γ → Cov A Γ'
wkCov wk w (ret x)
  = ret (wk w x)
wkCov wk w (ifte' e n m m₁)
  = ifte' (factor2Ext e w) (wkNe (factor2≤ e w) n) (wkCov wk w m) (wkCov wk w m₁)

fmapCov : (A →̇ B) → (Cov A →̇ Cov B)
fmapCov f (ret x) = ret (f x)
fmapCov f (ifte' e x m m₁) = ifte' e x (fmapCov f m) (fmapCov f m₁)

mapCov : (A ⇒' B) →̇ (Cov A ⇒' Cov B)
mapCov f w (ret x) = ret (f w x)
mapCov f w (ifte' e x m m₁) = ifte' e x (mapCov f w m) (mapCov f w m₁)

joinCov : Cov (Cov A) →̇ Cov A
joinCov (ret m) = m
joinCov (ifte' e x m m₁) = ifte' e x (joinCov m₁) (joinCov m₁)

bindCov : (A ⇒' Cov B) →̇ (Cov A ⇒' Cov B)
bindCov f e m = joinCov (mapCov f e m)

collect : Cov (NF a) →̇ NF a
collect (ret x) = x
collect (ifte' e x m m₁) = ifte e x (collect m) (collect m₁)

open import Data.Bool renaming (Bool to Bool')

TM' : Ty → (Ctx → Set)
TM' Unit = ⊤'
TM' 𝕔 = Cov (NE 𝕔)
TM' (a ⇒ b) = (TM' a) ⇒' (TM' b)
TM' (◻ a) = Box (TM' a)
TM' Bool = Cov (λ _ → Bool')

SUB' : Ctx → (Ctx → Set)
SUB' []       = ⊤'
SUB' (Γ `, a) = SUB' Γ ×' TM' a
SUB' (Γ 🔒)   = Lock (SUB' Γ)

-- values in the model can be weakened
wkTM' : Γ ⊆ Γ' → TM' a Γ → TM' a Γ'
wkTM' {a = 𝕔}  w m  = wkCov wkNe w m
wkTM' {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTM' {a = ◻ a}  w bx = λ e → wkTM' {a = a} (factor1≤ e w) (bx (factor1Ext e w))
wkTM' {a = Unit} w n  = tt
wkTM' {a = Bool} w n  = ret false

-- substitutions in the model can be weakened
wkSUB' : Γ ⊆ Γ' → SUB' Δ Γ → SUB' Δ Γ'
wkSUB' {Δ = []}     w tt          = tt
wkSUB' {Δ = Δ `, a} w (s , x)     = wkSUB' {Δ = Δ} w s , wkTM' {a = a} w x
wkSUB' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSUB' {Δ = Δ} (factor2≤ e w) s) (factor2Ext e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Box (TM' a) ΓL → CExt Γ ΓL ΓR → TM' a Γ
unbox' bx e = bx e


unboxCov : Cov (Box (TM' a)) Δ → CExt Γ Δ ΓR → Cov (TM' a) Γ
unboxCov (ret x) e
  = ret (x e)
unboxCov {a = a} (ifte' e' x m m₁) e
  = ifte' (extRAssoc e' e) x (unboxCov {a = a} m₁ e) (unboxCov {a = a} m₁ e)

appCov : Cov (TM' (a ⇒ b)) Γ → Cov (TM' a) Γ → Cov (TM' b) Γ
runCov : Cov (TM' a) →̇ TM' a

appCov {a = a} (ret f) m
  = ret (f idWk (runCov {a = a} m))
appCov {a = a} {b = b} (ifte' x x₁ f f₁) m
  = ifte' x x₁ (appCov {a = a} {b = b} f₁ m) (appCov {a = a} {b = b} f₁ m)

runCov {Unit}   m
  = tt
runCov {𝕔}      m
  = joinCov m
runCov {a ⇒ b} m
  = λ w x → runCov {b} (appCov {a = a} {b = b} (wkCov (wkTM' {a = a ⇒ b}) w m) (ret x))
runCov {◻ a}   m
  = λ e → runCov {a} (unboxCov {a = a} m e)
runCov {Bool}   m
  = joinCov m

-------------------------
-- Normalization function
-------------------------

VAR : Ty → Ctx → Set
VAR a Γ = Var Γ a

reify   : TM' a →̇ NF a
reflect : NE a  →̇ TM' a

reify {Unit} t = unit
reify {𝕔} t = collect (mapCov (λ _ n → up𝕔 n) idWk t)
reify {a ⇒ b} t = lam (reify {b} (t (drop idWk) (reflect {a} (var ze))))
reify {◻ a} t = box (reify (t (ext🔒- nil)))
reify {Bool} t = true

reflect {Unit} x = tt
reflect {𝕔} x = ret x
reflect {a ⇒ b} x = λ e t → reflect {b} (app (wkNe e x) (reify t))
reflect {◻ a} x = λ e → reflect (unbox x e)
reflect {Bool} x = ifte' nil x (ret true) (ret false)

-- identity substitution
idₛ' : SUB' Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, a} = wkSUB' {Δ = Γ} (drop idWk) (idₛ' {Γ = Γ}) , reflect {a} (var ze)
idₛ' {Γ 🔒}   = lock (idₛ' {Γ}) (ext🔒- nil)

-- interpretation of variables
substVar' : Var Γ a → (SUB' Γ →̇ TM' a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

unlock' : SUB' (Γ 🔒) Δ → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → SUB' Γ ΔL × CExt Δ ΔL ΔR }
unlock' (lock γ e) = _ , γ , e

CExt' : CExt Γ ΓL ΓR → SUB' Γ →̇ SUB' (ΓL 🔒)
CExt' nil       γ                         = lock γ nil
CExt' (ext e)   (γ , _)                   = CExt' e γ
CExt' {Γ = Γ} {ΓL} {ΓR} (ext🔒- e) (lock γ e') with unlock' {Γ = ΓL} (CExt' e γ) .snd
... | (γ' , e'') = lock γ' (extRAssoc e'' e')

eval-ifte : CExt Γ ΓL ΓR → Cov (λ _ → Bool') ΓL → Cov A Γ → Cov A Γ → Cov A Γ
eval-ifte e (ret false) m1 m2 = m2
eval-ifte e (ret true) m1 m2 = m2
eval-ifte e (ifte' x x₁ m m₁) m1 m2 = ifte' (extRAssoc x e) x₁ m2 m2

-- interpretation of terms
eval : Tm Γ a → (SUB' Γ →̇ TM' a)
eval (var x)                     s
  = substVar' x s
eval {Γ = Γ} (lam t)                     s
  = λ e x → eval t (wkSUB' {Δ = Γ} e s , x)
eval (app t u)                   s
  = (eval t s) idWk (eval u s)
eval (box t)                     s
  = λ e → eval t (lock s e)
eval {a = a} (unbox t nil)               s
  = unbox' {a = a} (eval t s) nil
eval (unbox t (ext e))           (s , _)
  = eval (unbox t e) s
eval (unbox t (ext🔒- e))         (lock s nil)
  = eval (unbox t e) s
eval {Γ} {a = a} (unbox t (ext🔒- e))         (lock s (ext {a = b} e'))
  = wkTM' {_} {_} {a} (fresh {a = b}) (eval (unbox t (ext🔒- e)) (lock s e'))
eval {a = a} (unbox t (ext🔒- nil))       (lock s (ext🔒- e'))
  = unbox' {a} (eval t s) (ext🔒- e')
eval (unbox t (ext🔒- (ext e)))   (lock (s , _) (ext🔒- e'))
  = eval (unbox t (ext🔒- e)) (lock s (ext🔒- e'))
eval (unbox t (ext🔒- (ext🔒- e))) (lock (lock s e'') (ext🔒- e'))
  = eval (unbox t (ext🔒- e)) (lock s (ext🔒- (extRAssoc e'' e')))
eval unit s = tt
eval true s = ret true
eval false s = ret false
eval {Γ = Γ} {a = a} (ifte {ΓL = ΓL} e t t₁ t₂) {Δ = Δ} s with unlock' {Γ = ΓL} (CExt' e s)
... | ((ΓL' , ΓR') , s' , e')
  = runCov {a = a} (eval-ifte e' (eval t s') (ret (eval t₁ s)) (ret (eval t₁ s)))

-- retraction of interpretation
quot : (SUB' Γ →̇ TM' a) → Nf Γ a
quot {Γ} f = reify (f (idₛ' {Γ}))

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
evalₛ : Sub Γ Δ → SUB' Γ  →̇ SUB' Δ
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

-- retraction of evalₛ
quotₛ : SUB' Γ →̇ Nfₛ- Γ
quotₛ {[]}     tt         = []
quotₛ {Γ `, _} (s , x)    = (quotₛ s) `, (reify x)
quotₛ {Γ 🔒}    (lock s e) = lock (quotₛ s) e

-- normalization function, for substitutions
normₛ : Sub Δ Γ → Nfₛ Δ Γ
normₛ {Δ} {Γ} s = quotₛ (evalₛ s (idₛ' {Δ}))
