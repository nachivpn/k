module IS4.Applications.Purity where

data Ty : Set where
  Unit : Ty
  𝕔    : Ty
  _⇒_ : Ty → Ty → Ty
  ◻_  : Ty → Ty

variable
    a b c d : Ty

open import Context (Ty) hiding (ext🔒) public

------------------------------------
-- Variables, terms and substituions
------------------------------------

-- Moggi's computational λ-calculus
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

  let-in : Tm Γ a → Tm (Γ `, a) b → Tm Γ b

  print : Tm Γ 𝕔 → Tm Γ Unit

wkTm : Γ ⊆ Γ' → Tm Γ a → Tm Γ' a
wkTm w (var x) = var (wkVar w x)
wkTm e (lam t) = lam (wkTm (keep e) t)
wkTm e (app t t₁) = app (wkTm e t) (wkTm e t₁)
wkTm e (box t) = box (wkTm (keep🔒 e) t)
wkTm w (unbox t e) = unbox (wkTm (factor2≤ e w) t) (factor2Ext e w)
wkTm e unit = unit
wkTm e (let-in t t₁) = let-in (wkTm e t) (wkTm (keep e) t₁)
wkTm e (print t) = print (wkTm e t)

import IS4.Applications.Metalanguage as Ml

data Nf : Ctx → Ty → Set
data Nc : Ctx → Ty → Set

data Nf where
  var   : Var Γ 𝕔 → Nf Γ 𝕔
  lam   : Nc (Γ `, a) b → Nf Γ (a ⇒ b)
  box   : Nc (Γ 🔒) a → Nf Γ (◻ a)
  unit  : Nf Γ Unit

data Nc where
  ret : Nf Γ a → Nc Γ a
  let-app-in : Var Γ (a ⇒ b) → Nf Γ a → Nc (Γ `, b) c → Nc Γ c
  let-print-in : Nf Γ 𝕔 → Nc (Γ `, Unit) a → Nc Γ a
  let-unbox-in : Var ΓL (◻ a) → CExt Γ ΓL ΓR → Nc (Γ `, a) b → Nc Γ b

-- embedding into terms

embNf : Nf Γ a → Tm Γ a
embNc : Nc Γ a → Tm Γ a

embNf (var x) = var x
embNf (lam x) = lam (embNc x)
embNf (box x) = box (embNc x)
embNf unit = unit

embNc (ret x) = embNf x
embNc (let-app-in x x₁ t) = let-in (app (var x) (embNf x₁)) (embNc t)
embNc (let-print-in x t) = let-in (print (embNf x)) (embNc t)
embNc (let-unbox-in x x₁ t) = let-in (unbox (var x) x₁) (embNc t)

-- weakening lemmas

wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a
wkNc : Γ ⊆ Γ' → Nc Γ a → Nc Γ' a

wkNf w t = {!!}

wkNc e t = {!!}

VAR NF NC : Ty → Ctx → Set
VAR a Γ = Var Γ a
NF a Γ = Nf Γ a
NC a Γ = Nc Γ a

------------
-- NbE Model
------------
open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)

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
  print : NF 𝕔 Γ → Print A (Γ `, Unit) → Print A Γ
  app   : VAR (a ⇒ b) Γ → NF a Γ → Print A (Γ `, b) → Print A Γ
  unbox : Var ΓL (◻ a) → CExt Γ ΓL ΓR → Print A (Γ `, a) → Print A Γ

wkPrint : (∀ {Δ} {Δ'} → (Δ ⊆ Δ') → A Δ → A Δ') → Γ ⊆ Γ' → Print A Γ → Print A Γ'
wkPrint f e (η x) = η (f e x)
wkPrint f e (print x p) = print (wkNf e x) (wkPrint f (keep e) p)
wkPrint f e (app x x₁ t) = app (wkVar e x) (wkNf e x₁) (wkPrint f (keep e) t)
wkPrint f e (unbox x x₁ t) = unbox  x {!!} (wkPrint f (keep e) t)

TM' : Ty → (Ctx → Set)
TM' Unit = ⊤'
TM' 𝕔 = NC 𝕔
TM' (a ⇒ b) = (TM' a) ⇒' Print (TM' b)
TM' (◻ a) = Box (Print (TM' a))

SUB' : Ctx → (Ctx → Set)
SUB' []       = ⊤'
SUB' (Γ `, a) = SUB' Γ ×' TM' a
SUB' (Γ 🔒)   = Lock (SUB' Γ)

-- values in the model can be weakened
wkTM' : Γ ⊆ Γ' → TM' a Γ → TM' a Γ'
wkTM' {a = 𝕔}  w n  = wkNc w n
wkTM' {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTM' {a = ◻ a}  w bx = λ e → wkPrint (wkTM' {a = a}) (factor1≤ e w) ((bx (factor1Ext e w)))
wkTM' {a = Unit} w n  = tt

-- substitutions in the model can be weakened
wkSUB' : Γ ⊆ Γ' → SUB' Δ Γ → SUB' Δ Γ'
wkSUB' {Δ = []}     w tt          = tt
wkSUB' {Δ = Δ `, a} w (s , x)     = wkSUB' {Δ = Δ} w s , wkTM' {a = a} w x
wkSUB' {Δ = Δ 🔒}    w (lock s e)  = lock (wkSUB' {Δ = Δ} (factor2≤ e w) s) (factor2Ext e w)

join : Print (Print A) →̇ Print A
join (η x) = x
join (print x x₁) = print x (join x₁)
join (app x x₁ x₂) = app x x₁ (join x₂)
join (unbox x x₁ x₂) = unbox x x₁ (join x₂)

fmap : (A →̇ B) → (Print A →̇ Print B)
fmap f (η x) = η (f x)
fmap f (print x m) = print x (fmap f m)
fmap f (app x x₁ m) = app x x₁ (fmap f m)
fmap f (unbox x x₁ m) = unbox x x₁ (fmap f m)

bind : (A →̇ Print B) → (Print A →̇ Print B)
bind f x = join (fmap f x)

fmap-int : (A ⇒' B) →̇ (Print A ⇒' Print B)
fmap-int f e (η x) = η (f e x)
fmap-int f e (print x m) = print x (fmap-int f (drop e) m)
fmap-int f e (app x x₁ m) = app x x₁ (fmap-int f (drop e) m)
fmap-int f e (unbox x x₁ m) = unbox x x₁ (fmap-int f (drop e) m)

bind-int : (A ⇒' Print B) →̇ (Print A ⇒' Print B)
bind-int f e (η x) = f e x
bind-int f e (print x m) = print x (bind-int f (drop e) m)
bind-int f e (app x x₁ m) = app x x₁ (bind-int f (drop e) m)
bind-int f e (unbox x x₁ m) = unbox x x₁ (bind-int f (drop e) m)

run : Print (NC a) →̇ NC a
run (η x) = x
run (print x x₁) = let-print-in x (run x₁)
run (app x x₁ x₂) = let-app-in x x₁ (run x₂)
run (unbox x x₁ x₂) = let-unbox-in x x₁ (run x₂)

runTM' : Print (TM' a) →̇ TM' a
runTM' {Unit} m = tt
runTM' {𝕔} m = run m
runTM' {a ⇒ b} m = λ e t → {!!}
runTM' {◻ a} m = λ e → {!!}

reflect : VAR a →̇ TM' a
reify : TM' a →̇ Print (NC a)

reify {Unit} x = η (ret unit)
reify {𝕔} x = η x
reify {a ⇒ b} {Γ} x = η (ret (lam (run (reify (runTM' {b} {Γ `, a} (x (drop idWk) (reflect {a} ze)))))))
reify {◻ a} t = η (ret (box (run (reify (runTM' {a} (t (ext🔒- nil)))))))

reflect {Unit} v = tt
reflect {𝕔} v = ret (var v)
reflect {a ⇒ b} v = λ e x → app (wkVar e v) {!!} (η (reflect {b} ze))
reflect {◻ a} v = λ e → unbox v e (η (reflect {a} ze))

-- semantic counterpart of `unbox` from `Tm`
unbox' : TM' (◻ a) ΓL → CExt Γ ΓL ΓR → TM' a Γ
unbox' bx e = {!!}

-- interpretation of variables
substVar' : Var Γ a → (SUB' Γ →̇ TM' a)
substVar' ze     (_ , x) = x
substVar' (su x) (γ , _) = substVar' x γ

-- interpretation of terms
eval : Tm Γ a → (SUB' Γ →̇ Print (TM' a))
eval (var x) s = η (substVar' x s)
eval {Γ = Γ} (lam t) s = η (λ e x → eval t ((wkSUB' {Δ = Γ} e s) , x))
eval (app {a = a} {b = b} t u) s = bind-int (λ e f → bind-int (λ e' x → f {!!} x) e (wkPrint (wkTM' {a = a}) e (eval u s))) idWk (eval t s)
eval (box t) s = η (λ e → eval t (lock s e))
eval (unbox t x) s = {!!}
eval unit s = η tt
eval (let-in t t₁) s = {!!}
eval (print t) s = print {!!} {!!}
