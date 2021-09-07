{-# OPTIONS --allow-unsolved-metas #-}
module Context (Ty : Set) where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; sym ; trans ; subst )

open _≡_

private
  variable
    a b c d : Ty

infixl 4 _🔒
infix  3 _≤_
infix  3 _,,_

open import Data.Empty using (⊥)
open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_ ; ∃ ; ∃₂)

-----------
-- Contexts
-----------

data Ctx : Set where
  []   : Ctx
  _`,_ : Ctx → Ty → Ctx
  _🔒   : Ctx → Ctx

[🔒] : Ctx
[🔒] = [] 🔒

variable
  Γ Δ Γ' Δ' ΓL ΓR : Ctx

-- append contexts (++)
_,,_ : Ctx → Ctx → Ctx
Γ ,, []       = Γ
Γ ,, (Δ `, x) = (Γ ,, Δ) `, x
Γ ,, (Δ 🔒)    = (Γ ,, Δ) 🔒

-- contexts free of locks
🔒-free : Ctx → Set
🔒-free []       = ⊤
🔒-free (Γ `, x) = 🔒-free Γ
🔒-free (Γ 🔒)    = ⊥

-- context to left of the last lock
←🔒 : Ctx → Ctx
←🔒 []       = []
←🔒 (Γ `, x) = ←🔒 Γ
←🔒 (Γ 🔒)    = Γ

-- context to the right of the last lock
🔒→ : Ctx → Ctx
🔒→ []       = []
🔒→ (Γ `, x) = 🔒→ Γ `, x
🔒→ (Γ 🔒)    = []


-------------
-- Weakenings
-------------

-- weakening relation
data _≤_  : Ctx → Ctx → Set where
  base   : [] ≤ []
  drop   : Γ ≤ Δ → (Γ `, a) ≤ Δ
  keep   : Γ ≤ Δ → (Γ `, a) ≤ (Δ `, a)
  keep🔒  : Γ ≤ Δ → Γ 🔒 ≤ Δ 🔒

{-
  Notes on _≤_:

  In addition to the regular definition of weakening (`base`, `drop` and `keep`),
  we also allow weakening in the presence of locks:

  - `keep🔒` allows weakening under locks

  Disallowing weakening with locks in general ensures that values
  that depend on "local" assumptions cannot be boxed by simply
  weakening with locks.

-}

-- weakening is reflexive
idWk : Γ ≤ Γ
idWk {[]}     = base
idWk {Γ `, x} = keep idWk
idWk {Γ 🔒}    = keep🔒 idWk

-- weakening is transitive (or can be composed)
_∙_ : {Σ : Ctx} → Δ ≤ Σ → Γ ≤ Δ → Γ ≤ Σ
w       ∙ base     = w
w       ∙ drop w'  = drop (w ∙ w')
drop w  ∙ keep w'  = drop (w ∙ w')
keep w  ∙ keep w'  = keep (w ∙ w')
keep🔒 w ∙ keep🔒 w' = keep🔒 (w ∙ w')

-- weakening that "generates a fresh variable"
fresh : (Γ `, a) ≤ Γ
fresh = drop idWk

variable
  ΓL' ΓR' Γ'' ΓL'' ΓR'' : Ctx
  ΔL ΔR : Ctx

data Flag : Set where tt ff : Flag

variable
  θ θ' : Flag

-- with locks?
WL : Flag → Set
WL tt = ⊤
WL ff = ⊥

------------
-- Variables
------------

data Var : Ctx → Ty → Set where
  ze : Var (Γ `, a) a
  su : (v : Var Γ a) → Var (Γ `, b) a

wkVar : Γ' ≤ Γ → Var Γ a → Var Γ' a
wkVar (drop e) ze     = su (wkVar e ze)
wkVar (keep e) ze     = ze
wkVar (drop e) (su v) = su (wkVar e (su v))
wkVar (keep e) (su v) = su (wkVar e v)

wkVarPresId : (x : Var Γ a) → wkVar idWk x ≡ x
wkVarPresId ze = refl
wkVarPresId (su x) = cong su (wkVarPresId x)

-- weakening a variable index increments
wkIncr : (x : Var Γ a) → wkVar (fresh {a = b}) x ≡ su x
wkIncr ze = refl
wkIncr (su x) = cong su (cong su (wkVarPresId x))

-- weakening of variables (a functor map) preserves weakening composition
wkVarPres∙ : (w : Γ' ≤ Γ) (w' : Δ ≤ Γ') (x : Var Γ a)
  → wkVar w' (wkVar w x) ≡ wkVar (w ∙ w') x
wkVarPres∙ (drop w) (drop w') ze     = cong su (wkVarPres∙ (drop w) w' ze)
wkVarPres∙ (drop w) (keep w') ze     = cong su (wkVarPres∙ w w' ze)
wkVarPres∙ (keep w) (drop w') ze     = cong su (wkVarPres∙ (keep w) w' ze)
wkVarPres∙ (keep w) (keep w') ze     = refl
wkVarPres∙ (drop w) (drop w') (su x) = cong su (wkVarPres∙ (drop w) w' (su x))
wkVarPres∙ (drop w) (keep w') (su x) = cong su (wkVarPres∙ w w' (su x))
wkVarPres∙ (keep w) (drop w') (su x) = cong su (wkVarPres∙ (keep w) w' (su x))
wkVarPres∙ (keep w) (keep w') (su x) = cong su (wkVarPres∙ w w' x)

-- weakening composition obeys the left identity law
leftIdWk : (w : Γ ≤ Γ') → idWk ∙ w ≡ w
leftIdWk base      = refl
leftIdWk (drop w)  = cong drop (leftIdWk w)
leftIdWk (keep w)  = cong keep (leftIdWk w)
leftIdWk (keep🔒 w) = cong keep🔒 (leftIdWk w)

-- weakening composition obeys the right identity law
rightIdWk : (w : Γ ≤ Γ') → w ∙ idWk ≡ w
rightIdWk base      = refl
rightIdWk (drop w)  = cong drop (rightIdWk w)
rightIdWk (keep w)  = cong keep (rightIdWk w)
rightIdWk (keep🔒 w) = cong keep🔒 (rightIdWk w)

-- weakening composition is associative
assocWk : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ3 ≤ Γ4) (w2 : Γ2 ≤ Γ3) → (w1 : Γ1 ≤ Γ2)
  → (w3 ∙ w2) ∙ w1 ≡ w3 ∙ (w2 ∙ w1)
assocWk w3         w2         base       = refl
assocWk w3         w2         (drop w1)  = cong drop (assocWk w3 w2 w1)
assocWk w3         (drop w2)  (keep w1)  = cong drop (assocWk w3 w2 w1)
assocWk (drop w3)  (keep w2)  (keep w1)  = cong drop (assocWk w3 w2 w1)
assocWk (keep w3)  (keep w2)  (keep w1)  = cong keep (assocWk w3 w2 w1)
assocWk (keep🔒 w3) (keep🔒 w2) (keep🔒 w1) = cong keep🔒 (assocWk w3 w2 w1)

--------------------
-- Context extension
--------------------

data Ext (θ : Flag) : Ctx → Ctx → Ctx → Set where
  nil  : Ext θ Γ Γ []
  ext  : Ext θ Γ ΓL ΓR → Ext θ (Γ `, a) ΓL (ΓR `, a)
  ext🔒 : WL θ → Ext θ Γ ΓL ΓR → Ext θ (Γ 🔒) ΓL (ΓR 🔒)

-- Lock free extension
LFExt : Ctx → Ctx → Ctx → Set
LFExt = Ext ff

-- Proof of WL is irrelevant
WLIsProp : (x x' : WL θ) → x ≡ x'
WLIsProp {tt} tt tt = refl

-- Proof of Ext is irrelevant
ExtIsProp : (e e' : Ext θ Γ ΓL ΓR) → e ≡ e'
ExtIsProp nil         nil         = refl
ExtIsProp (ext e)     (ext e')    = cong ext (ExtIsProp e e')
ExtIsProp (ext🔒 x e) (ext🔒 x' e') = cong₂ ext🔒 (WLIsProp x x') (ExtIsProp e e')

-- LFExt is indeed a lock-free extension
LFExtIs🔒-free : LFExt Γ ΓL ΓR → 🔒-free ΓR
LFExtIs🔒-free nil = tt
LFExtIs🔒-free (ext e) = LFExtIs🔒-free e

-- embed lock-free extensions into ones that extend with locks
upExt : Ext ff Γ ΓL ΓR → Ext θ Γ ΓL ΓR
upExt nil     = nil
upExt (ext e) = ext (upExt e)

-- extension is appending
extIs,, : Ext θ Γ ΓL ΓR → Γ ≡ (ΓL ,, ΓR)
extIs,, nil        = refl
extIs,, (ext e)    = cong (_`, _) (extIs,, e)
extIs,, (ext🔒 f e) = cong _🔒 (extIs,, e)

-- appending (potentially) with locks is an extension
,,IsExt : Ext tt (ΓL ,, ΓR) ΓL ΓR
,,IsExt {ΓL = ΓL} {[]}      = nil
,,IsExt {ΓL = ΓL} {ΓR `, x} = ext ,,IsExt
,,IsExt {ΓL = ΓL} {ΓR 🔒}    = ext🔒 tt ,,IsExt

-- appending without locks is an extension
,,IsExtLF : 🔒-free ΓR → Ext θ (ΓL ,, ΓR) ΓL ΓR
,,IsExtLF {[]} p = nil
,,IsExtLF {ΓR `, x} p = ext (,,IsExtLF p)

-- NOTE: `extIs,,` + `,,IsExt` implies that `Ext` is the call-graph of `_,,_`

-- extensions are unique
-- i.e., an extension of ΓL with ΓR must yield a unique extension
extUniq : Ext θ Γ' ΓL ΓR → Ext θ Γ ΓL ΓR → Γ' ≡ Γ
extUniq nil        nil         = refl
extUniq (ext e)    (ext e')    = cong (_`, _) (extUniq e e')
extUniq (ext🔒 f e) (ext🔒 _ e') = cong _🔒 (extUniq e e')

-- left identity of extension
extLId : Ext tt Γ [] Γ
extLId {Γ = []}     = nil
extLId {Γ = Γ `, x} = ext extLId
extLId {Γ = Γ 🔒}    = ext🔒 tt extLId

-- right identity of extension
extRId : Ext θ Γ Γ []
extRId = nil

-- lock-free extensions yield a "right" weakening (i.e., adding variables on the right)
LFExtTo≤ : LFExt Γ ΓL ΓR → Γ ≤ ΓL
LFExtTo≤ nil     = idWk
LFExtTo≤ (ext e) = drop (LFExtTo≤ e)

private
 variable ΓLL ΓLR ΓRL ΓRR : Ctx

-- extension is assocative
extLAssoc : Ext θ Γ ΓL ΓR  → Ext θ ΓR ΓRL ΓRR → Ext θ Γ (ΓL ,, ΓRL) ΓRR
extLAssoc el nil rewrite extIs,, el = nil
extLAssoc (ext el)    (ext er)      = ext (extLAssoc el er)
extLAssoc (ext🔒 x el) (ext🔒 _ er)   = ext🔒 x (extLAssoc el er)

-- extension is assocative
extRAssoc : Ext θ ΓL ΓLL ΓLR → Ext θ Γ ΓL ΓR → Ext θ Γ ΓLL (ΓLR ,, ΓR)
extRAssoc el nil         = el
extRAssoc el (ext er)    = ext (extRAssoc el er)
extRAssoc el (ext🔒 x er) = ext🔒 x (extRAssoc el er)

-------------------------------------
-- Operations on lock-free extensions
-------------------------------------

-- weaken the extension of a context
wkLFExt : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ' ≤ Γ → LFExt Γ' ((←🔒 Γ') 🔒) (🔒→ Γ')
wkLFExt e       (drop w)  = ext (wkLFExt e w)
wkLFExt nil     (keep🔒 w) = nil
wkLFExt (ext e) (keep w)  = ext (wkLFExt e w)

-- slice a weakening to the left of a lock
sliceLeft : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ' ≤ Γ → (←🔒 Γ') ≤ ΓL
sliceLeft e       (drop w)  = sliceLeft e w
sliceLeft nil     (keep🔒 w) = w
sliceLeft (ext e) (keep w)  = sliceLeft e w

-- slice a weakening to the right of a lock
sliceRight : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ' ≤ Γ → Γ' ≤ (←🔒 Γ') 🔒
sliceRight e w = LFExtTo≤ (wkLFExt e w)

-- the operation ←🔒 returns the context to the left of 🔒
←🔒IsPre🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓL ≡ (←🔒 Γ)
←🔒IsPre🔒 nil = refl
←🔒IsPre🔒 (ext e) = ←🔒IsPre🔒 e

-- the operation 🔒→ returns the context to the right of 🔒
🔒→isPost🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓR ≡ (🔒→ Γ)
🔒→isPost🔒 nil     = refl
🔒→isPost🔒 (ext e) = cong (_`, _) (🔒→isPost🔒 e)

-----------------------------------
-- Operations on general extensions
-----------------------------------

module carlostome/k/src/IS4/Term-agda where

  private

    _⊑_ = λ Γ Δ → ∃ λ Γ' → Ext tt Δ Γ Γ'

    pattern nil'       = _ , nil
    pattern ext' e     = _ , ext e
    pattern ext🔒' f e = _ , ext🔒 f e

    open import Relation.Binary hiding (_⇒_)

    ⊑-refl : Reflexive _⊑_
    ⊑-refl = nil'

    ⊑-trans : Transitive _⊑_
    ⊑-trans (_ , Γ⊑Δ) (_ , Δ⊑Ε) = _ , extRAssoc Γ⊑Δ Δ⊑Ε

    factor1 : Γ ⊑ Δ → Γ ≤ Γ' → ∃ λ Δ' → Δ ≤ Δ' × Γ' ⊑ Δ'
    factor1 nil'           Γ'≤Γ
      = _ , Γ'≤Γ , nil'
    factor1 (ext' Γ⊑Δ)     Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
    ... | Δ' , Δ'≤Δ , Γ'⊑Δ'
      = Δ' , drop Δ'≤Δ , Γ'⊑Δ'
    factor1 (ext🔒' _ Γ⊑Δ) Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
    ... | Δ' , Δ'≤Δ , Γ'⊑Δ'
      = (Δ' 🔒) , keep🔒 Δ'≤Δ , ⊑-trans Γ'⊑Δ' (ext🔒' tt extRId)

    factor2 : Γ ⊑ Δ → Δ' ≤ Δ → ∃ λ Γ' → Γ' ≤ Γ × Γ' ⊑ Δ'
    factor2 nil'           Δ≤Δ'
      = _ , Δ≤Δ' , nil'
    factor2 (ext' Γ⊑Δ)     Δ≤Δ'
      = factor2 (_ , Γ⊑Δ) (fresh ∙ Δ≤Δ')
    factor2 (ext🔒' _ Γ⊑Δ) Δ≤Δ' with factor2 (_ , Γ⊑Δ) (sliceLeft extRId Δ≤Δ')
    ... | Γ' , Γ≤Γ' , Γ'⊑Δ'
      = Γ' , Γ≤Γ' , ⊑-trans Γ'⊑Δ' (⊑-trans (ext🔒' tt extRId) (_ , upExt (wkLFExt extRId Δ≤Δ')))

-- f1LRCtx e w == proj₁ (factor1 (_ , e) w)
f1LRCtx : Ext tt Δ Γ ΓR → Γ ≤ Γ' → Ctx
f1LRCtx {Γ' = Γ'} nil        w = Γ'
f1LRCtx           (ext e)    w = f1LRCtx e w
f1LRCtx           (ext🔒 x e) w = (f1LRCtx e w) 🔒

-- f1RCtx e w == proj₁ (proj₂ (proj₂ (factor1 (_ , e) w)))
f1RCtx : Ext tt Δ Γ ΓR → Γ ≤ Γ' → Ctx
f1RCtx {Γ' = Γ'} nil        w = []
f1RCtx           (ext e)    w = f1RCtx e w
f1RCtx           (ext🔒 x e) w = (f1RCtx e w) 🔒

--
factor1Ext : (e : Ext tt Δ Γ ΓR) → (w : Γ ≤ Γ') → Ext tt (f1LRCtx e w) Γ' (f1RCtx e w)
factor1Ext nil        w = nil
factor1Ext (ext e)    w = factor1Ext e w
factor1Ext (ext🔒 x e) w = ext🔒 _ (factor1Ext e w)

--
factor1≤ : (e : Ext tt Δ Γ ΓR) → (w : Γ ≤ Γ') → Δ ≤ (f1LRCtx e w)
factor1≤ nil        w = w
factor1≤ (ext e)    w = drop (factor1≤ e w)
factor1≤ (ext🔒 x e) w = keep🔒 (factor1≤ e w)

-- f2LCtx e w == proj₁ (factor2 (_ , e) w)
f2LCtx : Ext θ Γ ΓL ΓR → Γ' ≤ Γ → Ctx
f2LCtx {Γ = Γ}      {Γ' = Γ'}       nil        w
  = Γ'
f2LCtx {Γ = Γ `, a} {Γ' = Γ' `, b}  (ext e)    (drop w)
  = f2LCtx e (fresh {Γ}  ∙ w)
f2LCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)    (keep w)
  = f2LCtx e w
f2LCtx {Γ = Γ 🔒} {Γ' = Γ' `, a}     (ext🔒 f e) (drop w)
  = f2LCtx  (ext🔒 f e) w
f2LCtx {Γ = Γ 🔒} {Γ' = Γ' 🔒}        (ext🔒 f e) (keep🔒 w)
  = f2LCtx e w

-- f2LCtx e w == proj₁ (proj₂ (proj₂ (factor2 (_ , e) w)))
f2RCtx : Ext θ Γ ΓL ΓR → Γ' ≤ Γ → Ctx
f2RCtx  {Γ = Γ}     {Γ' = Γ'}      nil        w
  = []
f2RCtx {Γ = Γ `, a} {Γ' = Γ' `, b} (ext e)    (drop w)
  = f2RCtx e (fresh ∙ w) `, b
f2RCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)   (keep w)
  = f2RCtx e w `, a
f2RCtx {Γ = Γ 🔒}    {Γ' = Γ' `, a} (ext🔒 f e) (drop  {a = a} w)
  = f2RCtx (ext🔒 f e) w `, a
f2RCtx {Γ = Γ 🔒}    {Γ' = Γ' 🔒}    (ext🔒 f e) (keep🔒 w)
  = (f2RCtx e w) 🔒

--
factor2Ext : (e : Ext θ Γ ΓL ΓR) → (w : Γ' ≤ Γ) → Ext θ Γ' (f2LCtx e w) (f2RCtx e w)
factor2Ext nil        w         = nil
factor2Ext (ext e)    (drop w)  = ext (factor2Ext e (fresh ∙ w))
factor2Ext (ext  e)   (keep w)  = ext (factor2Ext e w)
factor2Ext (ext🔒 f e) (drop w)  = ext (factor2Ext (ext🔒 f e) w)
factor2Ext (ext🔒 f e) (keep🔒 w) = ext🔒 f (factor2Ext e w)

--
factor2≤ : (e : Ext θ Γ ΓL ΓR) → (w : Γ' ≤ Γ) → (f2LCtx e w) ≤ ΓL
factor2≤ nil        w         = w
factor2≤ (ext e)    (drop w)  = factor2≤ e (fresh ∙ w)
factor2≤ (ext e)    (keep w)  = factor2≤ e w
factor2≤ (ext🔒 f e) (drop w)  = factor2≤ (ext🔒 f e) w
factor2≤ (ext🔒 f e) (keep🔒 w) = factor2≤ e w


----------------------------------------
-- Slicing laws for lock-free extensions
----------------------------------------

wkLFExtPres∙ : (w' : Δ ≤ Γ') (w  : Γ' ≤ Γ) (e : LFExt Γ (ΓL 🔒) ΓR)
  → wkLFExt (wkLFExt e w) w' ≡ wkLFExt e (w ∙ w')
wkLFExtPres∙ _ _ _ = ExtIsProp _ _

sliceLeftPres∙ : (w' : Δ ≤ Γ') (w  : Γ' ≤ Γ) (e : LFExt Γ (ΓL 🔒) ΓR)
  → (sliceLeft e w ∙ sliceLeft (wkLFExt e w) w') ≡ sliceLeft e (w ∙ w')
sliceLeftPres∙ (drop w')  (drop w)  nil     = sliceLeftPres∙ w' (drop w) nil
sliceLeftPres∙ (drop w')  (drop w)  (ext e) = sliceLeftPres∙ w' (drop w) (ext e)
sliceLeftPres∙ (keep w')  (drop w)  nil     = sliceLeftPres∙ w' w nil
sliceLeftPres∙ (keep w')  (drop w)  (ext e) = sliceLeftPres∙ w' w (ext e)
sliceLeftPres∙ (drop w')  (keep w)  (ext e) = sliceLeftPres∙ w' (keep w) (ext e)
sliceLeftPres∙ (keep w')  (keep w)  (ext e) = sliceLeftPres∙ w' w e
sliceLeftPres∙ (drop w')  (keep🔒 w) nil     = sliceLeftPres∙ w' (keep🔒 w) nil
sliceLeftPres∙ (keep🔒 w') (keep🔒 w) nil     = refl

-- roughly, slicing a weakening into two weakenings, one to left of the lock,
-- and the other to right, must not change its composition.
slicingLemma : (w : Γ' ≤ Γ) → (e : LFExt Γ (ΓL 🔒) ΓR)
  → LFExtTo≤ e ∙ w ≡ (keep🔒 (sliceLeft e w) ∙ sliceRight e w)
slicingLemma (drop w)  nil     = cong drop (slicingLemma w nil)
slicingLemma (drop w)  (ext e) = cong drop (slicingLemma w (ext e))
slicingLemma (keep w)  (ext e) = cong drop (slicingLemma w e)
slicingLemma (keep🔒 w) nil     = cong keep🔒 (trans (leftIdWk w) (sym (rightIdWk w)))

sliceLeftId : (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → sliceLeft e idWk ≡ idWk
sliceLeftId {Γ `, x} (ext e) = sliceLeftId e
sliceLeftId {Γ 🔒}    nil     = refl

wkLFExtPresId :  (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → wkLFExt e idWk ≡ e
wkLFExtPresId _ = ExtIsProp _ _

sliceRightId : (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → sliceRight e idWk ≡ LFExtTo≤ e
sliceRightId e rewrite wkLFExtPresId e = refl
