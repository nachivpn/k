{-# OPTIONS --safe --without-K #-}
module IS4.Applications.IS4Plus where

open import Relation.Nullary using (_because_; yes; no)

open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

-- IS4 with extensions

data Ty : Set where
  Unit : Ty
  𝕔    : Ty
  _⇒_  : Ty → Ty → Ty
  ◻_   : Ty → Ty
  Bool : Ty

variable
    a b c d : Ty

Ty-Decidable : Decidable (_≡_ {A = Ty})
Ty-Decidable Unit    Unit    = yes refl
Ty-Decidable Unit    Bool    = no  λ ()
Ty-Decidable Unit    𝕔       = no  λ ()
Ty-Decidable Unit    (a ⇒ b) = no  λ ()
Ty-Decidable Unit    (◻ a)   = no  λ ()
Ty-Decidable Bool    Unit    = no  λ ()
Ty-Decidable Bool    Bool    = yes refl
Ty-Decidable Bool    𝕔       = no  λ ()
Ty-Decidable Bool    (a ⇒ b) = no  λ ()
Ty-Decidable Bool    (◻ a)   = no  λ ()
Ty-Decidable 𝕔       Unit    = no  λ ()
Ty-Decidable 𝕔       Bool    = no  λ ()
Ty-Decidable 𝕔       𝕔       = yes refl
Ty-Decidable 𝕔       (a ⇒ b) = no  λ ()
Ty-Decidable 𝕔       (◻ a)   = no  λ ()
Ty-Decidable (a ⇒ b) Unit    = no  λ ()
Ty-Decidable (a ⇒ b) Bool    = no  λ ()
Ty-Decidable (a ⇒ b) 𝕔       = no  λ ()
Ty-Decidable (a ⇒ b) (c ⇒ d) with Ty-Decidable a c | Ty-Decidable b d
... | yes a≡c  | yes b≡d     = yes (cong₂ _⇒_ a≡c b≡d)
... | yes a≡c  | no  ¬b≡d    = no  λ { refl → ¬b≡d refl }
... | no  ¬a≡c | yes b≡d     = no  λ { refl → ¬a≡c refl }
... | no  ¬a≡c | no  ¬b≡d    = no  λ { refl → ¬a≡c refl }
Ty-Decidable (a ⇒ b) (◻ c)   = no  λ ()
Ty-Decidable (◻ a)   Unit    = no  λ ()
Ty-Decidable (◻ a)   Bool    = no  λ ()
Ty-Decidable (◻ a)   𝕔       = no  λ ()
Ty-Decidable (◻ a)   (b ⇒ c) = no  λ ()
Ty-Decidable (◻ a)   (◻ b)   with Ty-Decidable a b
... | yes a≡b                = yes (cong ◻_ a≡b)
... | no  ¬a≡b               = no  λ { refl → ¬a≡b refl }

import Context  Ty Ty-Decidable as Context hiding (ext#)
import Variable Ty              as Variable

open Context  public
open Variable public

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

  box   : Tm (Γ #) a
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
wkTm w (box t)     = box (wkTm (keep# w) t)
wkTm w (unbox t e) = unbox (wkTm (factorWk e w) t) (factorExt e w)
wkTm w unit = unit
wkTm w true = true
wkTm w false = false
wkTm w (ifte e t t₁ t₂) = ifte (factorExt e w) (wkTm (factorWk e w) t) (wkTm w t₁) (wkTm w t₂)

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
  up    : Ne Γ 𝕔 → Nf Γ 𝕔
  lam   : Nf (Γ `, a) b → Nf Γ (a ⇒ b)
  box   : Nf (Γ #) a → Nf Γ (◻ a)
  true  : Nf Γ Bool
  false : Nf Γ Bool
  ifte  : CExt Γ ΓL ΓR → Ne ΓL Bool → Nf Γ a → Nf Γ a → Nf Γ a
  unit  : Nf Γ Unit

-- embedding into terms

embNe : Ne Γ a → Tm Γ a
embNf : Nf Γ a → Tm Γ a

embNe (var x)     = var x
embNe (app m n)   = app (embNe m) (embNf n)
embNe (unbox n x) = unbox (embNe n) x

embNf (up  x)          = embNe x
embNf (lam n)          = lam (embNf n)
embNf (box n)          = box (embNf n)
embNf true             = true
embNf false            = false
embNf (ifte x x₁ n n₁) = ifte x true (embNf n) (embNf n₁)
embNf unit             = unit

-- weakening lemmas

wkNe : Γ ⊆ Γ' → Ne Γ a → Ne Γ' a
wkNf : Γ ⊆ Γ' → Nf Γ a → Nf Γ' a

wkNe w (var   x)   = var (wkVar w x)
wkNe w (app   m n) = app (wkNe w m) (wkNf w n)
wkNe w (unbox n e) = unbox (wkNe (factorWk e w) n) (factorExt e w)

wkNf w (up  x)         = up  (wkNe w x)
wkNf w (lam n)         = lam (wkNf (keep w) n)
wkNf w (box n)         = box (wkNf (keep# w) n)
wkNf w true            = true
wkNf w false           = false
wkNf w (ifte e m n n₁) = ifte (factorExt e w) (wkNe (factorWk e w) m) (wkNf w n) (wkNf w n₁)
wkNf w unit            = unit

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
Box A ΓL = {ΓL' Γ ΓR : Ctx} → ΓL ⊆ ΓL' → CExt Γ ΓL' ΓR → A Γ

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
  = ifte' (factorExt e w) (wkNe (factorWk e w) n) (wkCov wk w m) (wkCov wk w m₁)

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

Tm'- : Ty → (Ctx → Set)
Tm'- Unit    = ⊤'
Tm'- 𝕔       = Cov (NE 𝕔)
Tm'- (a ⇒ b) = (Tm'- a) ⇒' (Tm'- b)
Tm'- (◻ a)  = Box (Tm'- a)
Tm'- Bool    = Cov (λ _ → Bool')

Sub'- : Ctx → (Ctx → Set)
Sub'- []       = ⊤'
Sub'- (Γ `, a) = Sub'- Γ ×' Tm'- a
Sub'- (Γ #)    = Lock (Sub'- Γ)

-- values in the model can be weakened
wkTm'- : Γ ⊆ Γ' → Tm'- a Γ → Tm'- a Γ'
wkTm'- {a = 𝕔}     w m  = wkCov wkNe w m
wkTm'- {a = a ⇒ b} w f  = λ w' y → f (w ∙ w') y
wkTm'- {a = ◻ a}  w bx = λ w' e → bx (w ∙ w') e
wkTm'- {a = Unit}  w n  = tt
wkTm'- {a = Bool}  w m  = wkCov (λ _ z → z) w m

-- substitutions in the model can be weakened
wkSub'- : Γ ⊆ Γ' → Sub'- Δ Γ → Sub'- Δ Γ'
wkSub'- {Δ = []}     w tt          = tt
wkSub'- {Δ = Δ `, a} w (s , x)     = wkSub'- {Δ = Δ} w s , wkTm'- {a = a} w x
wkSub'- {Δ = Δ #}    w (lock s e)  = lock (wkSub'- {Δ = Δ} (factorWk e w) s) (factorExt e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Box (Tm'- a) ΓL → CExt Γ ΓL ΓR → Tm'- a Γ
unbox' bx e = bx idWk e

unboxCov : Cov (Box (Tm'- a)) Δ → CExt Γ Δ ΓR → Cov (Tm'- a) Γ
unboxCov (ret x) e
  = ret (x idWk e)
unboxCov {a = a} (ifte' e' x m1 m2) e
  = ifte' (extRAssoc e' e) x (unboxCov {a = a} m1 e) (unboxCov {a = a} m2 e)

appCov : Cov (Tm'- (a ⇒ b)) Γ → Cov (Tm'- a) Γ → Cov (Tm'- b) Γ
runCov : Cov (Tm'- a) →̇ Tm'- a

appCov {a = a} (ret f) m
  = ret (f idWk (runCov {a = a} m))
appCov {a = a} {b = b} (ifte' e n m1 m2) m
  = ifte' e n (appCov {a = a} {b = b} m1 m) (appCov {a = a} {b = b} m2 m)

runCov {Unit}   m
  = tt
runCov {𝕔}      m
  = joinCov m
runCov {a ⇒ b}  m
  = λ w x → runCov {b} (appCov {a = a} {b = b} (wkCov (wkTm'- {a = a ⇒ b}) w m) (ret x))
runCov {◻ a}   m
  = λ w e → runCov {a} (unboxCov {a = a} (wkCov (wkTm'- {a = ◻ a}) w m) e)
runCov {Bool}   m
  = joinCov m

-------------------------
-- Normalization function
-------------------------

VAR : Ty → Ctx → Set
VAR a Γ = Var Γ a

reify   : Tm'- a →̇ NF a
reflect : NE a  →̇ Tm'- a

reify {Unit}  x = unit
reify {𝕔}     x = collect (mapCov (λ _ n → up n) idWk x)
reify {a ⇒ b} x = lam (reify {b} (x (drop idWk) (reflect {a} (var zero))))
reify {◻ a}   x = box (reify (x idWk (ext#- nil)))
reify {Bool}  x = true

reflect {Unit}  n = tt
reflect {𝕔}     n = ret n
reflect {a ⇒ b} n = λ e t → reflect {b} (app (wkNe e n) (reify t))
reflect {◻ a}   n = λ w e → reflect (unbox (wkNe w n) e)
reflect {Bool}  n = ifte' nil n (ret true) (ret false)

-- identity substitution
idₛ' : Sub'- Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, a} = wkSub'- {Δ = Γ} (drop idWk) (idₛ' {Γ = Γ}) , reflect {a} (var zero)
idₛ' {Γ #}    = lock (idₛ' {Γ}) (ext#- nil)

-- interpretation of variables
substVar' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
substVar' zero     (_ , x) = x
substVar' (succ x) (γ , _) = substVar' x γ

unlock' : Sub'- (Γ #) Δ → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → Sub'- Γ ΔL × CExt Δ ΔL ΔR }
unlock' (lock γ e) = _ , γ , e

CExt' : CExt Γ ΓL ΓR → Sub'- Γ →̇ Sub'- (ΓL #)
CExt' nil       γ                         = lock γ nil
CExt' (ext e)   (γ , _)                   = CExt' e γ
CExt' {Γ = Γ} {ΓL} {ΓR} (ext#- e) (lock γ e') with unlock' {Γ = ΓL} (CExt' e γ) .snd
... | (γ' , e'') = lock γ' (extRAssoc e'' e')

eval-ifte : CExt Γ ΓL ΓR → Cov (λ _ → Bool') ΓL → Cov A Γ → Cov A Γ → Cov A Γ
eval-ifte e (ret false)        m1 m2 = m2
eval-ifte e (ret true)         m1 m2 = m2
eval-ifte e (ifte' e' n c1 c2) m1 m2  = ifte' (extRAssoc e' e) n (eval-ifte e c1 m1 m2) (eval-ifte e c2 m1 m2)

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval (var x)                       s
  = substVar' x s
eval {Γ = Γ} (lam t)               s
  = λ e x → eval t (wkSub'- {Δ = Γ} e s , x)
eval (app t u)                     s
  = (eval t s) idWk (eval u s)
eval {Γ = Γ} (box t)               s
  = λ w e → eval t (lock (wkSub'- {Δ = Γ} w s) e)
eval {a = a} (unbox t nil)         s
  = unbox' {a = a} (eval t s) nil
eval (unbox t (ext e))             (s , _)
  = eval (unbox t e) s
eval (unbox t (ext#- e))           (lock s nil)
  = eval (unbox t e) s
eval {a = a} (unbox t (ext#- e))   (lock s (ext {a = b} e'))
  = wkTm'- {_} {_} {a} fresh[ b ] (eval (unbox t (ext#- e)) (lock s e'))
eval {a = a} (unbox t (ext#- nil)) (lock s (ext#- e'))
  = unbox' {a} (eval t s) (ext#- e')
eval (unbox t (ext#- (ext e)))     (lock (s , _) (ext#- e'))
  = eval (unbox t (ext#- e)) (lock s (ext#- e'))
eval (unbox t (ext#- (ext#- e)))   (lock (lock s e'') (ext#- e'))
  = eval (unbox t (ext#- e)) (lock s (ext#- (extRAssoc e'' e')))
eval unit                          s
  = tt
eval true                          s
  = ret true
eval false                         s
  = ret false
eval {Γ = Γ} {a = a} (ifte {ΓL = ΓL} e t t₁ t₂) {Δ = Δ} s with unlock' {Γ = ΓL} (CExt' e s)
... | ((ΓL' , ΓR') , s' , e')
  = runCov {a = a} (eval-ifte e' (eval t s') (ret (eval t₁ s)) (ret (eval t₁ s)))

-- retraction of interpretation
quot : (Sub'- Γ →̇ Tm'- a) → Nf Γ a
quot {Γ} f = reify (f (idₛ' {Γ}))

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (eval t)
