module IS4.Applications.Purity where

data Ty : Set where
  Unit : Ty
  𝕔    : Ty
  _⇒_ : Ty → Ty → Ty
  ◻_  : Ty → Ty
  T   : Ty → Ty

variable
    a b c d : Ty

open import Context (Ty) hiding (ext🔒) public

------------------------------------
-- Variables, terms and substituions
------------------------------------

-- Moggi's monadic metalanguage
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

  ret : Tm Γ a → Tm Γ (T a)

  let-in : Tm Γ (T a) → Tm (Γ `, a) (T b) → Tm Γ (T b)

  print : Tm Γ 𝕔 → Tm Γ (T Unit)

TM : Ty → Ctx → Set
TM a Γ = Tm Γ a

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x)     = var (wkVar w x)
wkTm w (lam t)     = lam (wkTm (keep w) t)
wkTm w (app t u)   = app (wkTm w t) (wkTm w u)
wkTm w (box t)     = box (wkTm (keep🔒 w) t)
wkTm w (unbox t e) = unbox (wkTm (factor2≤ e w) t) (factor2Ext e w)
wkTm w unit = unit
wkTm w (print t) = print (wkTm w t)
wkTm w (let-in t u) = let-in (wkTm w t) (wkTm (keep w) u)
wkTm w (ret t) = ret (wkTm w t)

open import IS4.Substitution Ty Tm var wkTm public

-- apply substitution to a term
substTm : Sub Δ Γ → Tm Γ a → Tm Δ a
substTm s                                (var x)
  = substVar s x
substTm s                                (lam t)
  = lam (substTm (wkSub fresh s `, var ze) t)
substTm s                                (app t u)
  = app (substTm s t) (substTm s u)
substTm s                                (box t)
  = box (substTm (lock s (ext🔒- nil)) t)
substTm s                                (unbox t nil)
  = unbox (substTm s t) nil
substTm (s `, _)                         (unbox t (ext e))
  = substTm s (unbox t e)
substTm (lock s nil)                     (unbox t (ext🔒- e))
  = substTm s (unbox t e)
substTm (lock s (ext e'))                (unbox t (ext🔒- e))
  = wkTm fresh (substTm (lock s e') (unbox t (ext🔒- e)))
substTm (lock s (ext🔒- e'))             (unbox t (ext🔒- nil))
  = unbox (substTm s t) (ext🔒- e')
substTm (lock (s `, _) (ext🔒- e'))      (unbox t (ext🔒- (ext e)))
  = substTm (lock s (ext🔒- e')) (unbox t (ext🔒- e))
substTm (lock (lock s e'') (ext🔒- e')) (unbox t (ext🔒- (ext🔒- e)))
  = substTm (lock s (ext🔒- (extRAssoc e'' e'))) (unbox t (ext🔒- e))
substTm s                                unit
  = unit
substTm s                                (print t)
  = print (substTm s t)
substTm s                                (let-in t u)
  = let-in (substTm s t) (substTm (wkSub fresh s `, var ze) u)
substTm s (ret t) = ret (substTm s t)

-- substitution composition
_∙ₛ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
[]                          ∙ₛ s'
  = []
(s `, t)                    ∙ₛ s'
  = (s ∙ₛ s') `, substTm s' t
lock s nil                  ∙ₛ s'
  = lock (s ∙ₛ s') nil
lock s (ext e)              ∙ₛ (s' `, _)
  = lock s e ∙ₛ s'
lock s (ext🔒- nil)        ∙ₛ lock s' e'
  = lock (s ∙ₛ s') e'
lock s (ext🔒- (ext e))    ∙ₛ lock (s' `, _) e'
  = lock s (ext🔒- e) ∙ₛ lock s' e'
lock s (ext🔒- (ext🔒- e)) ∙ₛ lock (lock s' e'') e'
  = lock s (ext🔒- e) ∙ₛ lock s' (extRAssoc e'' e')

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)

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
  ret : Nf Γ a → Nf Γ (T a)
  let-in : Ne Γ (T a) → Nf (Γ `, a) (T b) → Nf Γ (T b)
  unit : Nf Γ Unit
  print : Nf Γ 𝕔 → Nf Γ (T Unit)
  let-print-in : Ne Γ 𝕔 → Nf (Γ `, Unit) (T b) → Nf Γ (T b)

-- embedding into terms

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var x)     = var x
embNe (app m n)   = app (embNe m) (embNf n)
embNe (unbox n x) = unbox (embNe n) x

embNf (up𝕔 x) = embNe x
embNf (lam n) = lam (embNf n)
embNf (box n) = box (embNf n)
embNf (ret t) = ret (embNf t)
embNf (let-in n t) = let-in (embNe n) (embNf t)
embNf unit = unit
embNf (print t) = print (embNf t)
embNf (let-print-in x t) = let-in (print (embNe x)) (embNf t)

-- weakening lemmas

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var x)      = var (wkVar w x)
wkNe w (app m n)    = app (wkNe w m) (wkNf w n)
wkNe w (unbox n e)  = unbox (wkNe (factor2≤ e w) n) (factor2Ext e w)

wkNf e (up𝕔 x) = up𝕔 (wkNe e x)
wkNf e (lam n) = lam (wkNf (keep e) n)
wkNf e (box n) = box (wkNf (keep🔒 e) n)
wkNf e (ret t) = ret (wkNf e t)
wkNf e (let-in x t) = let-in (wkNe e x) (wkNf (keep e) t)
wkNf e unit = unit
wkNf e (print t) = print (wkNf e t)
wkNf e (let-print-in x t) = let-print-in (wkNe e x) (wkNf (keep e) t)

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

data Print (A : Ctx → Set) : Ctx → Set where
  η     : A →̇ Print A
  print : NE 𝕔 Γ → Print A (Γ `, Unit) → Print A Γ
  bind  : NE (T a) Γ → Print A (Γ `, a) → Print A Γ

wkPrint : (∀ {Δ} {Δ'} → (Δ ⊆ Δ') → A Δ → A Δ') → Γ ⊆ Γ' → Print A Γ → Print A Γ'
wkPrint f e (η x) = η (f e x)
wkPrint f e (print x p) = print (wkNe e x) (wkPrint f (keep e) p)
wkPrint f e (bind x p) = bind (wkNe e x) (wkPrint f (keep e) p)

TM' : Ty → (Ctx → Set)
TM' Unit = ⊤'
TM' 𝕔 = NE 𝕔
TM' (a ⇒ b) = (TM' a) ⇒' (TM' b)
TM' (◻ a) = Box (TM' a)
TM' (T a) = Print (TM' a)

SUB' : Ctx → (Ctx → Set)
SUB' []       = ⊤'
SUB' (Γ `, a) = SUB' Γ ×' TM' a
SUB' (Γ 🔒)   = Lock (SUB' Γ)

-- values in the model can be weakened
wkTM' : Γ ⊆ Γ' → TM' a Γ → TM' a Γ'
wkTM' {a = 𝕔}  w n  = wkNe w n
wkTM' {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTM' {a = ◻ a}  w bx = λ e → wkTM' {a = a} (factor1≤ e w) (bx (factor1Ext e w))
wkTM' {a = Unit} w n  = tt
wkTM' {a = T a} w n  = wkPrint (wkTM' {a = a}) w n

-- substitutions in the model can be weakened
wkSUB' : Γ ⊆ Γ' → SUB' Δ Γ → SUB' Δ Γ'
wkSUB' {Δ = []}     w tt          = tt
wkSUB' {Δ = Δ `, a} w (s , x)     = wkSUB' {Δ = Δ} w s , wkTM' {a = a} w x
wkSUB' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSUB' {Δ = Δ} (factor2≤ e w) s) (factor2Ext e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : TM' (◻ a) ΓL → CExt Γ ΓL ΓR → TM' a Γ
unbox' bx e = bx e

mapPrint  : (A ⇒' B) →̇ (Print A ⇒' Print B)
mapPrint f e (η x) = η (f e x)
mapPrint f e (print x m) = print x (mapPrint f (drop e) m)
mapPrint f e (bind x m) = bind x (mapPrint f (drop e) m)

joinPrint : Print (Print A) →̇ Print A
joinPrint (η x) = x
joinPrint (print x x₁) = print x (joinPrint x₁)
joinPrint (bind x x₁) = bind x (joinPrint x₁)

bindPrint : (A ⇒' Print B) →̇ (Print A ⇒' Print B) 
bindPrint f e m = joinPrint (mapPrint f e m)

-------------------------
-- Normalization function
-------------------------

VAR : Ty → Ctx → Set
VAR a Γ = Var Γ a

reify-Print : Print (TM' a) →̇ NF (T a)
reify   : TM' a →̇ NF a
reflect : NE a  →̇ TM' a

reify {Unit} t = unit
reify {𝕔} t = up𝕔 t
reify {a ⇒ b} t = lam (reify {b} (t (drop idWk) (reflect {a} (var ze))))
reify {◻ a} t = box (reify (t (ext🔒- nil)))
reify {T a} t = reify-Print t

reify-Print (η x) = ret (reify x)
reify-Print (print x u) = let-print-in x (reify-Print u)
reify-Print (bind x x₁) = let-in x (reify-Print x₁)

reflect {Unit} x = tt
reflect {𝕔} x = x
reflect {a ⇒ b} x = λ e t → reflect {b} (app (wkNe e x) (reify t))
reflect {◻ a} x = λ e → reflect (unbox x e)
reflect {T a} x = bind x (η (reflect {a} (var ze)))

-- identity substitution
idₛ' : SUB' Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, a} = wkSUB' {Δ = Γ} (drop idWk) (idₛ' {Γ = Γ}) , reflect {a} (var ze)
idₛ' {Γ 🔒}   = lock (idₛ' {Γ}) (ext🔒- nil)

-- interpretation of variables
substVar' : Var Γ a → (SUB' Γ →̇ TM' a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

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
eval (ret t) s = η (eval t s)
eval {Γ = Γ} (let-in t u) s = bindPrint (λ e x → eval u ((wkSUB' {Δ = Γ} e s) , x)) idWk (eval t s)
eval (print t) s = print (eval t s) (η tt)

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

module _ where
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product using (∃)
  open import Relation.Binary.PropositionalEquality

  noClosedNe : Ne [] a → ⊥
  noClosedNe (app n x) = noClosedNe n
  noClosedNe (unbox n nil) = noClosedNe n
  
  noClosedNe🔒 : Ne ([] 🔒) a → ⊥
  noClosedNe🔒 (app n _) = noClosedNe🔒 n
  noClosedNe🔒 (unbox n Ext.nil) = noClosedNe🔒 n
  noClosedNe🔒 (unbox n (Ext.ext🔒 _ Ext.nil)) = noClosedNe n
  
  purity : (t : Nf [] (T (◻ Unit))) → t ≡ ret (box unit)
  purity (ret (box unit)) = refl
  purity (let-in x t) = ⊥-elim (noClosedNe x)
  purity (let-print-in x t) = ⊥-elim (noClosedNe x)
