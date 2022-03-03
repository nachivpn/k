module Context (Ty : Set) where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; cong ; cong₂ ; sym ; trans ; subst ; subst₂)

open _≡_

private
  variable
    a b c d : Ty

infixl 6 _🔒 _`,_
infix  5 _⊆_
infixl 5 _,,_

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_ ; ∃ ; ∃₂ ; proj₂)

-----------
-- Contexts
-----------

data Ctx : Set where
  []   : Ctx
  _`,_ : (Γ : Ctx) → (a : Ty) → Ctx
  _🔒   : (Γ : Ctx) → Ctx

[🔒] : Ctx
[🔒] = [] 🔒

variable
  Γ Γ' Γ'' ΓL ΓR : Ctx
  Δ Δ' Δ'' ΔL ΔR : Ctx
  Θ Θ' Θ'' ΘL ΘR : Ctx
  Ξ Ξ' Ξ'' ΞL ΞR : Ctx

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
data _⊆_  : Ctx → Ctx → Set where
  base   : [] ⊆ []
  drop   : Γ ⊆ Δ → Γ ⊆ (Δ `, a)
  keep   : Γ ⊆ Δ → (Γ `, a) ⊆ (Δ `, a)
  keep🔒  : Γ ⊆ Δ → Γ 🔒 ⊆ Δ 🔒

{-
  Notes on _≤_:

  In addition to the regular definition of weakening (`base`, `drop` and `keep`),
  we also allow weakening in the presence of locks:

  - `keep🔒` allows weakening under locks

  Disallowing weakening with locks in general ensures that values
  that depend on "local" assumptions cannot be boxed by simply
  weakening with locks.

-}

variable
  w w' w'' : Γ ⊆ Γ'

-- weakening is reflexive
idWk[_] : (Γ : Ctx) → Γ ⊆ Γ
idWk[_] []       = base
idWk[_] (Γ `, x) = keep idWk[ Γ ]
idWk[_] (Γ 🔒)    = keep🔒 idWk[ Γ ]

idWk = λ {Γ} → idWk[ Γ ]

-- weakening is transitive (or can be composed)
_∙_ : Θ ⊆ Δ → Δ ⊆ Γ → Θ ⊆ Γ
w       ∙ base     = w
w       ∙ drop w'  = drop (w ∙ w')
drop w  ∙ keep w'  = drop (w ∙ w')
keep w  ∙ keep w'  = keep (w ∙ w')
keep🔒 w ∙ keep🔒 w' = keep🔒 (w ∙ w')

-- weakening that "generates a fresh variable"
fresh : Γ ⊆ (Γ `, a)
fresh = drop idWk

variable
  ΓL' ΓR' ΓL'' ΓR'' : Ctx

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

pattern v0 = ze
pattern v1 = su v0
pattern v2 = su v1

wkVar : Γ ⊆ Γ' → Var Γ a → Var Γ' a
wkVar (drop e) v      = su (wkVar e v)
wkVar (keep e) ze     = ze
wkVar (keep e) (su v) = su (wkVar e v)

-- OBS: in general, Γ ⊈ Δ ,, Γ
leftWkVar : (v : Var Γ a) → Var (Δ ,, Γ) a
leftWkVar ze     = ze
leftWkVar (su v) = su (leftWkVar v)

wkVarPresId : (x : Var Γ a) → wkVar idWk x ≡ x
wkVarPresId ze = refl
wkVarPresId (su x) = cong su (wkVarPresId x)

-- weakening a variable index increments
wkIncr : (x : Var Γ a) → wkVar (fresh {a = b}) x ≡ su x
wkIncr ze = refl
wkIncr (su x) = cong su (cong su (wkVarPresId x))

-- weakening of variables (a functor map) preserves weakening composition
wkVarPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (x : Var Γ a)
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
leftIdWk : (w : Γ' ⊆ Γ) → idWk ∙ w ≡ w
leftIdWk base      = refl
leftIdWk (drop w)  = cong drop (leftIdWk w)
leftIdWk (keep w)  = cong keep (leftIdWk w)
leftIdWk (keep🔒 w) = cong keep🔒 (leftIdWk w)

-- weakening composition obeys the right identity law
rightIdWk : (w : Γ' ⊆ Γ) → w ∙ idWk ≡ w
rightIdWk base      = refl
rightIdWk (drop w)  = cong drop (rightIdWk w)
rightIdWk (keep w)  = cong keep (rightIdWk w)
rightIdWk (keep🔒 w) = cong keep🔒 (rightIdWk w)

-- weakening composition is associative
assocWk : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ4 ⊆ Γ3) (w2 : Γ3 ⊆ Γ2) → (w1 : Γ2 ⊆ Γ1)
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
  ext  : (e : Ext θ Γ ΓL ΓR) → Ext θ (Γ `, a) ΓL (ΓR `, a)
  ext🔒 : WL θ → (e : Ext θ Γ ΓL ΓR) → Ext θ (Γ 🔒) ΓL (ΓR 🔒)

-- Lock-Free Extension
LFExt : Ctx → Ctx → Ctx → Set
LFExt = Ext ff

-- Context Extension (potentially with locks)
CExt : Ctx → Ctx → Ctx → Set
CExt = Ext tt

pattern ext🔒- e = ext🔒 tt e

variable
  e e' e'' : Ext θ Γ ΓL ΓR

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
upLFExt : LFExt Γ ΓL ΓR → Ext θ Γ ΓL ΓR
upLFExt nil     = nil
upLFExt (ext e) = ext (upLFExt e)

-- extension is appending
extIs,, : Ext θ Γ ΓL ΓR → Γ ≡ (ΓL ,, ΓR)
extIs,, nil        = refl
extIs,, (ext e)    = cong (_`, _) (extIs,, e)
extIs,, (ext🔒 f e) = cong _🔒 (extIs,, e)

-- appending (potentially) with locks is an extension
,,IsExt : CExt (ΓL ,, ΓR) ΓL ΓR
,,IsExt {ΓL = ΓL} {[]}      = nil
,,IsExt {ΓL = ΓL} {ΓR `, x} = ext ,,IsExt
,,IsExt {ΓL = ΓL} {ΓR 🔒}    = ext🔒 tt ,,IsExt

-- appending without locks is an extension
,,IsExtLF : 🔒-free ΓR → LFExt (ΓL ,, ΓR) ΓL ΓR
,,IsExtLF {[]} p = nil
,,IsExtLF {ΓR `, x} p = ext (,,IsExtLF p)

-- NOTE: `extIs,,` + `,,IsExt` implies that `Ext` is the call-graph of `_,,_`

-- extensions are unique
-- i.e., an extension of ΓL with ΓR must yield a unique extension
extLUniq : Ext θ Γ' ΓL ΓR → Ext θ Γ ΓL ΓR → Γ' ≡ Γ
extLUniq nil        nil         = refl
extLUniq (ext e)    (ext e')    = cong (_`, _) (extLUniq e e')
extLUniq (ext🔒 f e) (ext🔒 _ e') = cong _🔒 (extLUniq e e')

`,-injective-left : Γ `, a ≡ Δ `, b → Γ ≡ Δ
`,-injective-left refl = refl

`,-injective-right : Γ `, a ≡ Δ `, b → a ≡ b
`,-injective-right refl = refl

🔒-injective : Γ 🔒 ≡ Δ 🔒 → Γ ≡ Δ
🔒-injective refl = refl

private
  open import Data.Nat
  open import Data.Nat.Properties

  m≢n+1+m : ∀ m {n} → m ≢ n + suc m
  m≢n+1+m m m≡n+1+m = m≢1+m+n m (trans m≡n+1+m (+-comm _ (suc m)))

  length : (Γ : Ctx) → ℕ
  length []       = 0
  length (Γ `, a) = 1 + length Γ
  length (Γ 🔒)    = 1 + length Γ

  lengthPres+ : ∀ Γ Δ → length (Γ ,, Δ) ≡ length Δ + length Γ
  lengthPres+ Γ []       = refl
  lengthPres+ Γ (Δ `, a) = cong suc (lengthPres+ Γ Δ)
  lengthPres+ Γ (Δ 🔒)    = cong suc (lengthPres+ Γ Δ)

  module _ {A : Set} where
    Γ≡Γ,a-impossible₁ : Γ ≡ Γ `, a ,, Γ' → A
    Γ≡Γ,a-impossible₁ {Γ} {a} {Γ'} p = ⊥-elim (m≢n+1+m (length Γ) (trans (cong length p) (lengthPres+ (Γ `, a) Γ')))

    Γ≡Γ,a-impossible₂ : Γ ≡ Γ ,, Γ' `, a → A
    Γ≡Γ,a-impossible₂ {Γ} {Γ'} {a} p = ⊥-elim (m≢1+n+m (length Γ) (trans (cong length p) (cong suc (lengthPres+ Γ Γ'))))

    Γ≡Γ🔒-impossible₁ : Γ ≡ Γ 🔒 ,, Γ' → A
    Γ≡Γ🔒-impossible₁ {Γ} {Γ'} p = ⊥-elim (m≢n+1+m (length Γ) (trans (cong length p) (lengthPres+ (Γ 🔒) Γ')))

    Γ≡Γ🔒-impossible₂ : Γ ≡ (Γ ,, Γ') 🔒 → A
    Γ≡Γ🔒-impossible₂ {Γ} {Γ'} p = ⊥-elim (m≢1+n+m (length Γ) (trans (cong length p) (cong suc (lengthPres+ Γ Γ'))))

    Γ,aRΓ-impossible : Ext θ Γ (Γ `, a) ΓR → A
    Γ,aRΓ-impossible e = Γ≡Γ,a-impossible₁ (extIs,, e)

    Γ🔒RΓ-impossible : Ext θ Γ (Γ 🔒) ΓR → A
    Γ🔒RΓ-impossible e = Γ≡Γ🔒-impossible₁ (extIs,, e)

,,-injective-right : Δ ,, Γ ≡ Δ ,, Γ' → Γ ≡ Γ'
,,-injective-right {Δ} {[]}     {[]}       p = refl
,,-injective-right {Δ} {[]}     {Γ' `, a}  p = Γ≡Γ,a-impossible₂ p
,,-injective-right {Δ} {[]}     {Γ' 🔒}    p = Γ≡Γ🔒-impossible₂ p
,,-injective-right {Δ} {Γ `, a} {[]}       p = Γ≡Γ,a-impossible₂ (sym p)
,,-injective-right {Δ} {Γ `, a} {Γ' `, b}  p = cong₂ _`,_ (,,-injective-right (`,-injective-left p)) (`,-injective-right p)
,,-injective-right {Δ} {Γ 🔒}   {[]}       p = Γ≡Γ🔒-impossible₂ (sym p)
,,-injective-right {Δ} {Γ 🔒}   {Γ' 🔒}    p = cong _🔒 (,,-injective-right (🔒-injective p))

extRUniq : Ext θ Γ ΓL ΓR → Ext θ Γ ΓL ΓR' → ΓR ≡ ΓR'
extRUniq e e' = ,,-injective-right (trans (sym (extIs,, e)) (extIs,, e'))

-- left identity of extension
extLId : CExt Γ [] Γ
extLId {Γ = []}     = nil
extLId {Γ = Γ `, x} = ext extLId
extLId {Γ = Γ 🔒}    = ext🔒 tt extLId

-- right identity of extension
extRId : Ext θ Γ Γ []
extRId = nil

-- lock-free extensions yield a "right" weakening (i.e., adding variables on the right)
LFExtTo≤ : LFExt Γ ΓL ΓR → ΓL ⊆ Γ
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

,,-assoc : (ΓLL ,, ΓLR) ,, ΓR ≡ ΓLL ,, (ΓLR ,, ΓR)
,,-assoc {ΓLL} {ΓLR} {ΓR} = extIs,, {θ = tt} {ΓR = ΓLR ,, ΓR} (extRAssoc {ΓLR = ΓLR} ,,IsExt ,,IsExt)

,,-leftUnit : {Γ : Ctx} → [] ,, Γ ≡ Γ
,,-leftUnit {[]} = refl
,,-leftUnit {Γ `, a} = cong (_`, _) ,,-leftUnit
,,-leftUnit {Γ 🔒} = cong _🔒 ,,-leftUnit

extLeftUnit : extRAssoc nil e ≡ subst (CExt _ _) (sym ,,-leftUnit) e
extLeftUnit = ExtIsProp _ _

-------------------------------------
-- Operations on lock-free extensions
-------------------------------------

-- weaken the extension of a context
wkLFExt : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ ⊆ Γ' → LFExt Γ' ((←🔒 Γ') 🔒) (🔒→ Γ')
wkLFExt e       (drop w)  = ext (wkLFExt e w)
wkLFExt nil     (keep🔒 w) = nil
wkLFExt (ext e) (keep w)  = ext (wkLFExt e w)

-- left weaken the (lock-free) extension of a context
leftWkLFExt : (e : LFExt Γ ΓL ΓR) → LFExt (Δ ,, Γ) (Δ ,, ΓL) ΓR
leftWkLFExt nil     = nil
leftWkLFExt (ext e) = ext (leftWkLFExt e)

-- left unweaken the (lock-free) extension of a context
leftUnwkLFExt : (e : LFExt (Δ ,, Γ) (Δ ,, ΓL) ΓR) → LFExt Γ ΓL ΓR
leftUnwkLFExt {Δ} {Γ} {ΓL} {ΓR} e = subst (λ Γ → LFExt Γ ΓL ΓR) obs (,,IsExtLF (LFExtIs🔒-free e))
  where
    obs : ΓL ,, ΓR ≡ Γ
    obs = ,,-injective-right (sym (extIs,, (extRAssoc ,,IsExt (upLFExt e))))

-- slice a weakening to the left of a lock
sliceLeft : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ ⊆ Γ' → ΓL ⊆ (←🔒 Γ')
sliceLeft e       (drop w)  = sliceLeft e w
sliceLeft nil     (keep🔒 w) = w
sliceLeft (ext e) (keep w)  = sliceLeft e w

-- slice a weakening to the right of a lock
sliceRight : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ ⊆ Γ' → (←🔒 Γ') 🔒 ⊆ Γ'
sliceRight e w = LFExtTo≤ (wkLFExt e w)

-- the operation ←🔒 returns the context to the left of 🔒
←🔒IsPre🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓL ≡ (←🔒 Γ)
←🔒IsPre🔒 nil = refl
←🔒IsPre🔒 (ext e) = ←🔒IsPre🔒 e

-- the operation 🔒→ returns the context to the right of 🔒
🔒→isPost🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓR ≡ (🔒→ Γ)
🔒→isPost🔒 nil     = refl
🔒→isPost🔒 (ext e) = cong (_`, _) (🔒→isPost🔒 e)

----------------------------------------
-- Slicing laws for lock-free extensions
----------------------------------------

wkLFExtPres∙ : (w' : Γ' ⊆ Δ) (w  : Γ ⊆ Γ') (e : LFExt Γ (ΓL 🔒) ΓR)
  → wkLFExt (wkLFExt e w) w' ≡ wkLFExt e (w ∙ w')
wkLFExtPres∙ _ _ _ = ExtIsProp _ _

sliceLeftPres∙ : (w' : Γ' ⊆ Δ) (w  : Γ ⊆ Γ') (e : LFExt Γ (ΓL 🔒) ΓR)
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
slicingLemma : (w : Γ ⊆ Γ') → (e : LFExt Γ (ΓL 🔒) ΓR)
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

-----------------------------------
-- Operations on general extensions
-----------------------------------

module _ where

  private

    _R_ = λ Γ Δ → ∃ λ Γ' → CExt Δ Γ Γ'

    pattern nil⊑     = _ , nil
    pattern ext⊑ e    = _ , ext e
    pattern ext🔒⊑ f e = _ , ext🔒 f e

    open import Relation.Binary hiding (_⇒_)

    ⊑-refl : Reflexive _R_
    ⊑-refl = nil⊑

    ⊑-trans : Transitive _R_
    ⊑-trans (_ , Γ⊑Δ) (_ , Δ⊑Ε) = _ , extRAssoc Γ⊑Δ Δ⊑Ε

    -- we don't use factor1 anymore
    factor1 : Γ R Δ → Γ' ⊆ Γ → ∃ λ Δ' → Δ' ⊆ Δ × Γ' R Δ'
    factor1 nil⊑           Γ'≤Γ
      = _ , Γ'≤Γ , nil⊑
    factor1 (ext⊑ Γ⊑Δ)     Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
    ... | Δ' , Δ'≤Δ , Γ'⊑Δ'
      = Δ' , drop Δ'≤Δ , Γ'⊑Δ'
    factor1 (ext🔒⊑ _ Γ⊑Δ) Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
    ... | Δ' , Δ'≤Δ , Γ'⊑Δ'
      = (Δ' 🔒) , keep🔒 Δ'≤Δ , ⊑-trans Γ'⊑Δ' (ext🔒⊑ tt extRId)

    -- not used directly, but serves as a specification of
    -- what is expected from factorExt and factorWk
    factor2 : Γ R Δ → Δ ⊆ Δ' → ∃ λ Γ' → Γ ⊆ Γ' × Γ' R Δ'
    factor2 nil⊑           Δ≤Δ'
      = _ , Δ≤Δ' , nil⊑
    factor2 (ext⊑ Γ⊑Δ)     Δ≤Δ'
      = factor2 (_ , Γ⊑Δ) (fresh ∙ Δ≤Δ')
    factor2 (ext🔒⊑ _ Γ⊑Δ) Δ≤Δ' with factor2 (_ , Γ⊑Δ) (sliceLeft extRId Δ≤Δ')
    ... | Γ' , Γ≤Γ' , Γ'⊑Δ'
      = Γ' , Γ≤Γ' , ⊑-trans Γ'⊑Δ' (⊑-trans (ext🔒⊑ tt extRId) (_ , upLFExt (wkLFExt extRId Δ≤Δ')))

-- "Left" context of factoring (see type of factorExt)
-- lCtx e w == proj₁ (factor2 (_ , e) w)
lCtx : CExt Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
lCtx {Γ = Γ}      {Γ' = Γ'}       nil        w
  = Γ'
lCtx {Γ = Γ `, a} {Γ' = Γ' `, b}  (ext e)    (drop w)
  = lCtx (ext e) w
lCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)    (keep w)
  = lCtx e w
lCtx {Γ = Γ 🔒} {Γ' = Γ' `, a}     (ext🔒- e) (drop w)
  = lCtx  (ext🔒- e) w
lCtx {Γ = Γ 🔒} {Γ' = Γ' 🔒}        (ext🔒- e) (keep🔒 w)
  = lCtx e w

-- "Right" context of factoring (see type of factorExt)
-- rCtx e w == proj₁ (proj₂ (proj₂ (factor2 (_ , e) w)))
rCtx : CExt Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
rCtx  {Γ = Γ}     {Γ' = Γ'}      nil       w
  = []
rCtx {Γ = Γ `, a} {Γ' = Γ' `, b} (ext e)   (drop w)
  = rCtx (ext e) w `, b
rCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)  (keep w)
  = rCtx e w `, a
rCtx {Γ = Γ 🔒}    {Γ' = Γ' `, a} (ext🔒- e) (drop  {a = a} w)
  = rCtx (ext🔒- e) w `, a
rCtx {Γ = Γ 🔒}    {Γ' = Γ' 🔒}    (ext🔒- e) (keep🔒 w)
  = (rCtx e w) 🔒

-- factorExt e w == proj₂ (proj₂ (proj₂ (factor2 (_ , e) w)))
factorExt : (e : CExt Γ ΓL ΓR) → (w : Γ ⊆ Γ') → CExt Γ' (lCtx e w) (rCtx e w)
factorExt nil       w         = nil
factorExt (ext e)   (drop w)  = ext (factorExt (ext e) w)
factorExt (ext  e)  (keep w)  = ext (factorExt e w)
factorExt (ext🔒- e) (drop w)  = ext (factorExt (ext🔒- e) w)
factorExt (ext🔒- e) (keep🔒 w) = ext🔒- (factorExt e w)

-- factorWk e w == proj₁ (proj₂ (factor2 (_ , e) w))
factorWk : (e : CExt Γ ΓL ΓR) → (w : Γ ⊆ Γ') → ΓL ⊆ (lCtx e w)
factorWk nil       w         = w
factorWk (ext e)   (drop w)  = factorWk (ext e) w
factorWk (ext e)   (keep w)  = factorWk e w
factorWk (ext🔒- e) (drop w)  = factorWk (ext🔒- e) w
factorWk (ext🔒- e) (keep🔒 w) = factorWk e w

--------------------------------------------
-- Factorisation laws for general extensions
--------------------------------------------

lCtxPresId : (e : CExt Γ ΓL ΓR) → lCtx e idWk ≡ ΓL
lCtxPresId nil       = refl
lCtxPresId (ext e)   = lCtxPresId e
lCtxPresId (ext🔒- e) = lCtxPresId e

rCtxPresId : (e : CExt Γ ΓL ΓR) → rCtx e idWk ≡ ΓR
rCtxPresId nil       = refl
rCtxPresId (ext e)   = cong (_`, _) (rCtxPresId e)
rCtxPresId (ext🔒- e) = cong _🔒 (rCtxPresId e)

factorWkPresId : (e : CExt Γ ΓL ΓR) → subst (ΓL ⊆_) (lCtxPresId e) (factorWk e idWk) ≡ idWk[ ΓL ]
factorWkPresId nil       = refl
factorWkPresId (ext e)   = factorWkPresId e
factorWkPresId (ext🔒- e) = factorWkPresId e

factorExtPresId : (e : CExt Γ ΓL ΓR) → subst₂ (CExt Γ) (lCtxPresId e) (rCtxPresId e) (factorExt e idWk) ≡ e
factorExtPresId _ = ExtIsProp _ _

lCtxPres∙ : (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → lCtx e (w ∙ w') ≡ lCtx (factorExt e w) w'
lCtxPres∙ nil         w           w'         = refl
lCtxPres∙ e@(ext _)   w@(drop _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext _)   w@(keep _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext🔒- _) w@(drop _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext🔒- _) w@(keep🔒 _) (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext _)   (drop w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext🔒- _) (drop w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ (ext e)     (keep w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ (ext🔒- e)   (keep🔒 w)   (keep🔒 w') = lCtxPres∙ e w w'

rCtxPres∙ : (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → rCtx e (w ∙ w') ≡ rCtx (factorExt e w) w'
rCtxPres∙ nil         w           w'         = refl
rCtxPres∙ e@(ext _)   w@(drop _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext _)   w@(keep _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext🔒- _) w@(drop _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext🔒- _) w@(keep🔒 _) (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext _)   (drop w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext🔒- _) (drop w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ (ext e)     (keep w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ (ext🔒- e)   (keep🔒 w)   (keep🔒 w') = cong _🔒 (rCtxPres∙ e w w')

factorWkPres∙ : ∀ (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → subst (ΓL ⊆_) (lCtxPres∙ e w w') (factorWk e (w ∙ w')) ≡ factorWk e w ∙ factorWk (factorExt e w) w'
factorWkPres∙ nil         w           w'         = refl
factorWkPres∙ e@(ext _)   w@(drop _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext _)   w@(keep _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext🔒- _) w@(drop _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext🔒- _) w@(keep🔒 _) (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext _)   (drop w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext🔒- _) (drop w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ (ext e)     (keep w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ (ext🔒- e)   (keep🔒 w)   (keep🔒 w') = factorWkPres∙ e w w'

factorExtPres∙ : ∀ (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → subst₂ (CExt Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')) ≡ factorExt (factorExt e w) w'
factorExtPres∙ _ _ _ = ExtIsProp _ _

lCtxPresRefl : ∀ (w : Γ ⊆ Γ') → lCtx (nil {Γ = Γ}) w ≡ Γ'
lCtxPresRefl _w = refl

rCtxPresRefl : ∀ (w : Γ ⊆ Γ') → rCtx (nil {Γ = Γ}) w ≡ []
rCtxPresRefl _w = refl

factorWkPresRefl : ∀ (w : Γ ⊆ Γ') → subst (Γ ⊆_) (lCtxPresRefl w) (factorWk (nil {Γ = Γ}) w) ≡ w
factorWkPresRefl _w = refl

factorExtPresRefl : ∀ (w : Γ ⊆ Γ') → subst₂ (CExt Γ') (lCtxPresRefl w) (rCtxPresRefl w) (factorExt (nil {Γ = Γ}) w) ≡ nil {Γ = Γ'}
factorExtPresRefl _w = ExtIsProp _ _

lCtxPresTrans : ∀ (e : CExt Δ Γ ΓR) (e' : CExt Θ Δ ΔR) (w : Θ ⊆ Θ') → lCtx (extRAssoc e e') w ≡ lCtx e (factorWk e' w)
lCtxPresTrans _e nil          _w        = refl
lCtxPresTrans e  e'@(ext _)   (drop w)  = lCtxPresTrans e e' w
lCtxPresTrans e  (ext e')     (keep w)  = lCtxPresTrans e e' w
lCtxPresTrans e  e'@(ext🔒- _) (drop w)  = lCtxPresTrans e e' w
lCtxPresTrans e  (ext🔒- e')   (keep🔒 w) = lCtxPresTrans e e' w

rCtxPresTrans : ∀ (e : CExt Δ Γ ΓR) (e' : CExt Θ Δ ΔR) (w : Θ ⊆ Θ') → rCtx (extRAssoc e e') w ≡ rCtx e (factorWk e' w) ,, rCtx e' w
rCtxPresTrans _e nil         _w               = refl
rCtxPresTrans e e'@(ext _)   (drop {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e (ext e')     (keep {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e e'@(ext🔒- _) (drop {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e (ext🔒- e')   (keep🔒 w)        = cong (_🔒) (rCtxPresTrans e e' w)

factorWkPresTrans : ∀ (e : CExt Δ Γ ΓR) (e' : CExt Θ Δ ΔR) (w : Θ ⊆ Θ') → subst (Γ ⊆_) (lCtxPresTrans e e' w) (factorWk (extRAssoc e e') w) ≡ factorWk e (factorWk e' w)
factorWkPresTrans _e nil          _w        = refl
factorWkPresTrans e  e'@(ext _)   (drop w)  = factorWkPresTrans e e' w
factorWkPresTrans e  (ext e')     (keep w)  = factorWkPresTrans e e' w
factorWkPresTrans e  e'@(ext🔒- _) (drop w)  = factorWkPresTrans e e' w
factorWkPresTrans e  (ext🔒- e')   (keep🔒 w) = factorWkPresTrans e e' w

factorExtPresTrans : ∀ (e : CExt Δ Γ ΓR) (e' : CExt Θ Δ ΔR) (w : Θ ⊆ Θ') → subst₂ (CExt Θ') (lCtxPresTrans e e' w) (rCtxPresTrans e e' w) (factorExt (extRAssoc e e') w) ≡ extRAssoc (factorExt e (factorWk e' w)) (factorExt e' w)
factorExtPresTrans _e _e' _w = ExtIsProp _ _
