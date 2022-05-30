module Context (Ty : Set) where

private
  variable
    a b c d : Ty

infixl 6 _🔒 _`,_
infix  5 _⊆_
infixl 5 _,,_

open import Data.Empty   using (⊥ ; ⊥-elim)
open import Data.Product using (Σ ; _×_ ; _,_ ; ∃ ; ∃₂ ; proj₂)
open import Data.Unit    using (⊤ ; tt)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; subst ; subst₂ ; cong ; cong₂)

open import PEUtil

-----------
-- Contexts
-----------

data Ctx : Set where
  []   : Ctx
  _`,_ : (Γ : Ctx) → (a : Ty) → Ctx
  _🔒   : (Γ : Ctx) → Ctx

[🔒] : Ctx
[🔒] = [] 🔒

[_] : Ty → Ctx
[_] a = [] `, a

variable
  Γ Γ' Γ'' ΓL ΓR ΓR' : Ctx
  Δ Δ' Δ'' ΔL ΔR ΔR' : Ctx
  Θ Θ' Θ'' ΘL ΘR ΘR' : Ctx
  Ξ Ξ' Ξ'' ΞL ΞR ΞR' : Ctx

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
  drop   : Γ ⊆ Δ → Γ ⊆ Δ `, a
  keep   : Γ ⊆ Δ → Γ `, a ⊆ Δ `, a
  keep🔒  : Γ ⊆ Δ → Γ 🔒 ⊆ Δ 🔒

{-
  Notes on _⊆_:

  In addition to the regular definition of weakening (`base`, `drop` and `keep`),
  we also allow weakening in the presence of locks:

  - `keep🔒` allows weakening under locks

  Disallowing weakening with locks in general ensures that values
  that depend on "local" assumptions cannot be boxed by simply
  weakening with locks.

-}

drop[_] = λ {Γ} {Δ} a → drop {Γ} {Δ} {a}

keep[_] = λ {Γ} {Δ} a → keep {Γ} {Δ} {a}

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
fresh : Γ ⊆ Γ `, a
fresh = drop idWk

fresh[_] = λ {Γ} a → fresh {Γ} {a}

variable
  ΓL' ΓL'' ΓR'' : Ctx

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
wkIncr : (x : Var Γ a) → wkVar fresh[ b ] x ≡ su x
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

fresh-keep : fresh[ a ] ∙ keep[ a ] w ≡ w ∙ fresh[ a ]
fresh-keep = cong drop (trans˘ (leftIdWk _) (rightIdWk _))

--------------------
-- Context extension
--------------------

data Ext (θ : Flag) : Ctx → Ctx → Ctx → Set where
  nil  : Ext θ Γ Γ []
  ext  : (e : Ext θ Γ ΓL ΓR) → Ext θ (Γ `, a) ΓL (ΓR `, a)
  ext🔒 : WL θ → (e : Ext θ Γ ΓL ΓR) → Ext θ (Γ 🔒) ΓL (ΓR 🔒)

nil[_] = λ {θ} Γ → nil {θ} {Γ}

ext[_] = λ {θ} {Γ} {ΓL} {ΓR} a → ext {θ} {Γ} {ΓL} {ΓR} {a}

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

ExtIsProp′ : (e : Ext θ Γ ΓL ΓR) → (e' : Ext θ Γ ΓL ΓR') → subst (Ext θ Γ ΓL) (extRUniq e e') e ≡ e'
ExtIsProp′ _ _ = ExtIsProp _ _

-- left identity of extension
extLId : CExt Γ [] Γ
extLId {Γ = []}     = nil
extLId {Γ = Γ `, x} = ext extLId
extLId {Γ = Γ 🔒}    = ext🔒 tt extLId

-- right identity of extension
extRId : Ext θ Γ Γ []
extRId = nil

-- extension that "generates a fresh variable"
freshExt : Ext θ (Γ `, a) Γ ([] `, a)
freshExt = ext nil

freshExt[_] = λ {θ} {Γ} a → freshExt {θ} {Γ} {a}

-- lock-free extensions yield a "right" weakening (i.e., adding variables on the right)
LFExtTo⊆ : LFExt Γ ΓL ΓR → ΓL ⊆ Γ
LFExtTo⊆ nil     = idWk
LFExtTo⊆ (ext e) = drop (LFExtTo⊆ e)

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
sliceRight e w = LFExtTo⊆ (wkLFExt e w)

-- the operation ←🔒 returns the context to the left of 🔒
←🔒IsPre🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓL ≡ (←🔒 Γ)
←🔒IsPre🔒 nil = refl
←🔒IsPre🔒 (ext e) = ←🔒IsPre🔒 e

-- the operation 🔒→ returns the context to the right of 🔒
🔒→isPost🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓR ≡ (🔒→ Γ)
🔒→isPost🔒 nil     = refl
🔒→isPost🔒 (ext e) = cong (_`, _) (🔒→isPost🔒 e)

LFExtTo⊆PresTrans : (e : LFExt ΓL ΓLL ΓLR) (e' : LFExt Γ ΓL ΓR)
  → LFExtTo⊆ (extRAssoc e e') ≡ LFExtTo⊆ e ∙ LFExtTo⊆ e'
LFExtTo⊆PresTrans e nil      = sym (rightIdWk (LFExtTo⊆ e))
LFExtTo⊆PresTrans e (ext e') = cong drop (LFExtTo⊆PresTrans e e')

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
  → LFExtTo⊆ e ∙ w ≡ (keep🔒 (sliceLeft e w) ∙ sliceRight e w)
slicingLemma (drop w)  nil     = cong drop (slicingLemma w nil)
slicingLemma (drop w)  (ext e) = cong drop (slicingLemma w (ext e))
slicingLemma (keep w)  (ext e) = cong drop (slicingLemma w e)
slicingLemma (keep🔒 w) nil     = cong keep🔒 (trans (leftIdWk w) (sym (rightIdWk w)))

sliceLeftId : (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → sliceLeft e idWk ≡ idWk
sliceLeftId {Γ `, x} (ext e) = sliceLeftId e
sliceLeftId {Γ 🔒}    nil     = refl

wkLFExtPresId :  (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → wkLFExt e idWk ≡ e
wkLFExtPresId _ = ExtIsProp _ _

sliceRightId : (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → sliceRight e idWk ≡ LFExtTo⊆ e
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
    factor1 nil⊑           Γ'⊆Γ
      = _ , Γ'⊆Γ , nil⊑
    factor1 (ext⊑ Γ⊑Δ)     Γ'⊆Γ with factor1 (_ , Γ⊑Δ) Γ'⊆Γ
    ... | Δ' , Δ'⊆Δ , Γ'⊑Δ'
      = Δ' , drop Δ'⊆Δ , Γ'⊑Δ'
    factor1 (ext🔒⊑ _ Γ⊑Δ) Γ'⊆Γ with factor1 (_ , Γ⊑Δ) Γ'⊆Γ
    ... | Δ' , Δ'⊆Δ , Γ'⊑Δ'
      = (Δ' 🔒) , keep🔒 Δ'⊆Δ , ⊑-trans Γ'⊑Δ' (ext🔒⊑ tt extRId)

    -- not used directly, but serves as a specification of
    -- what is expected from factorExt and factorWk
    factor2 : Γ R Δ → Δ ⊆ Δ' → ∃ λ Γ' → Γ ⊆ Γ' × Γ' R Δ'
    factor2 nil⊑           Δ⊆Δ'
      = _ , Δ⊆Δ' , nil⊑
    factor2 (ext⊑ Γ⊑Δ)     Δ⊆Δ'
      = factor2 (_ , Γ⊑Δ) (fresh ∙ Δ⊆Δ')
    factor2 (ext🔒⊑ _ Γ⊑Δ) Δ⊆Δ' with factor2 (_ , Γ⊑Δ) (sliceLeft extRId Δ⊆Δ')
    ... | Γ' , Γ⊆Γ' , Γ'⊑Δ'
      = Γ' , Γ⊆Γ' , ⊑-trans Γ'⊑Δ' (⊑-trans (ext🔒⊑ tt extRId) (_ , upLFExt (wkLFExt extRId Δ⊆Δ')))

-- "Left" context of factoring (see type of factorExt)
-- lCtx e w == proj₁ (factor2 (_ , e) w)
lCtx : Ext θ Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
lCtx {Γ = Γ}      {Γ' = Γ'}       nil        w
  = Γ'
lCtx {Γ = Γ `, a} {Γ' = Γ' `, b}  (ext e)    (drop w)
  = lCtx (ext e) w
lCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)    (keep w)
  = lCtx e w
lCtx {Γ = Γ 🔒} {Γ' = Γ' `, a}     (ext🔒 f e) (drop w)
  = lCtx  (ext🔒 f e) w
lCtx {Γ = Γ 🔒} {Γ' = Γ' 🔒}        (ext🔒 f e) (keep🔒 w)
  = lCtx e w

-- "Right" context of factoring (see type of factorExt)
-- rCtx e w == proj₁ (proj₂ (proj₂ (factor2 (_ , e) w)))
rCtx : Ext θ Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
rCtx  {Γ = Γ}     {Γ' = Γ'}      nil        w
  = []
rCtx {Γ = Γ `, a} {Γ' = Γ' `, b} (ext e)    (drop w)
  = rCtx (ext e) w `, b
rCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)   (keep w)
  = rCtx e w `, a
rCtx {Γ = Γ 🔒}    {Γ' = Γ' `, a} (ext🔒 f e) (drop {a = a} w)
  = rCtx (ext🔒 f e) w `, a
rCtx {Γ = Γ 🔒}    {Γ' = Γ' 🔒}    (ext🔒 f e) (keep🔒 w)
  = (rCtx e w) 🔒

-- factorExt e w == proj₂ (proj₂ (proj₂ (factor2 (_ , e) w)))
factorExt : (e : Ext θ Γ ΓL ΓR) → (w : Γ ⊆ Γ') → Ext θ Γ' (lCtx e w) (rCtx e w)
factorExt nil        w         = nil
factorExt (ext e)    (drop w)  = ext (factorExt (ext e) w)
factorExt (ext  e)   (keep w)  = ext (factorExt e w)
factorExt (ext🔒 f e) (drop w)  = ext (factorExt (ext🔒 f e) w)
factorExt (ext🔒 f e) (keep🔒 w) = ext🔒 f (factorExt e w)

-- factorWk e w == proj₁ (proj₂ (factor2 (_ , e) w))
factorWk : (e : Ext θ Γ ΓL ΓR) → (w : Γ ⊆ Γ') → ΓL ⊆ (lCtx e w)
factorWk nil        w         = w
factorWk (ext e)    (drop w)  = factorWk (ext e) w
factorWk (ext e)    (keep w)  = factorWk e w
factorWk (ext🔒 f e) (drop w)  = factorWk (ext🔒 f e) w
factorWk (ext🔒 f e) (keep🔒 w) = factorWk e w

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

lCtxPres∙ : (e : Ext θ Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → lCtx e (w ∙ w') ≡ lCtx (factorExt e w) w'
lCtxPres∙ nil          w           w'         = refl
lCtxPres∙ e@(ext _)    w@(drop _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext _)    w@(keep _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext🔒 f _) w@(drop _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext🔒 f _) w@(keep🔒 _) (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext _)    (drop w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext🔒 f _) (drop w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ (ext e)      (keep w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ (ext🔒 f e)   (keep🔒 w)   (keep🔒 w') = lCtxPres∙ e w w'

rCtxPres∙ : (e : Ext θ Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → rCtx e (w ∙ w') ≡ rCtx (factorExt e w) w'
rCtxPres∙ nil          w           w'         = refl
rCtxPres∙ e@(ext _)    w@(drop _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext _)    w@(keep _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext🔒 f _) w@(drop _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext🔒 f _) w@(keep🔒 _) (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext _)    (drop w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext🔒 f _) (drop w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ (ext e)      (keep w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ (ext🔒 f e)   (keep🔒 w)   (keep🔒 w') = cong _🔒 (rCtxPres∙ e w w')

factorWkPres∙ : ∀ (e : Ext θ Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → subst (ΓL ⊆_) (lCtxPres∙ e w w') (factorWk e (w ∙ w')) ≡ factorWk e w ∙ factorWk (factorExt e w) w'
factorWkPres∙ nil          w           w'         = refl
factorWkPres∙ e@(ext _)    w@(drop _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext _)    w@(keep _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext🔒 f _) w@(drop _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext🔒 f _) w@(keep🔒 _) (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext _)    (drop w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext🔒 f _) (drop w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ (ext e)      (keep w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ (ext🔒 f e)   (keep🔒 w)   (keep🔒 w') = factorWkPres∙ e w w'

factorExtPres∙ : ∀ (e : Ext θ Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → subst₂ (Ext θ Γ'') (lCtxPres∙ e w w') (rCtxPres∙ e w w') (factorExt e (w ∙ w')) ≡ factorExt (factorExt e w) w'
factorExtPres∙ _ _ _ = ExtIsProp _ _

lCtxPresRefl : ∀ (w : Γ ⊆ Γ') → lCtx {θ} (nil {Γ = Γ}) w ≡ Γ'
lCtxPresRefl _w = refl

rCtxPresRefl : ∀ (w : Γ ⊆ Γ') → rCtx {θ} (nil {Γ = Γ}) w ≡ []
rCtxPresRefl _w = refl

factorWkPresRefl : ∀ (w : Γ ⊆ Γ') → subst (Γ ⊆_) (lCtxPresRefl {θ = θ} w) (factorWk {θ = θ} (nil {Γ = Γ}) w) ≡ w
factorWkPresRefl _w = refl

factorExtPresRefl : ∀ (w : Γ ⊆ Γ') → subst₂ (Ext θ Γ') (lCtxPresRefl {θ = θ} w) (rCtxPresRefl {θ = θ} w) (factorExt (nil {Γ = Γ}) w) ≡ nil {Γ = Γ'}
factorExtPresRefl _w = ExtIsProp _ _

lCtxPresTrans : ∀ (e : Ext θ Δ Γ ΓR) (e' : Ext θ Θ Δ ΔR) (w : Θ ⊆ Θ') → lCtx (extRAssoc e e') w ≡ lCtx e (factorWk e' w)
lCtxPresTrans _e nil           _w        = refl
lCtxPresTrans e  e'@(ext _)    (drop w)  = lCtxPresTrans e e' w
lCtxPresTrans e  (ext e')      (keep w)  = lCtxPresTrans e e' w
lCtxPresTrans e  e'@(ext🔒 f _) (drop w)  = lCtxPresTrans e e' w
lCtxPresTrans e  (ext🔒 f e')   (keep🔒 w) = lCtxPresTrans e e' w

rCtxPresTrans : ∀ (e : Ext θ Δ Γ ΓR) (e' : Ext θ Θ Δ ΔR) (w : Θ ⊆ Θ') → rCtx (extRAssoc e e') w ≡ rCtx e (factorWk e' w) ,, rCtx e' w
rCtxPresTrans _e nil          _w               = refl
rCtxPresTrans e e'@(ext _)    (drop {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e (ext e')      (keep {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e e'@(ext🔒 f _) (drop {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e (ext🔒 f e')   (keep🔒 w)        = cong (_🔒) (rCtxPresTrans e e' w)

factorWkPresTrans : ∀ (e : Ext θ Δ Γ ΓR) (e' : Ext θ Θ Δ ΔR) (w : Θ ⊆ Θ') → subst (Γ ⊆_) (lCtxPresTrans e e' w) (factorWk (extRAssoc e e') w) ≡ factorWk e (factorWk e' w)
factorWkPresTrans _e nil           _w        = refl
factorWkPresTrans e  e'@(ext _)    (drop w)  = factorWkPresTrans e e' w
factorWkPresTrans e  (ext e')      (keep w)  = factorWkPresTrans e e' w
factorWkPresTrans e  e'@(ext🔒 f _) (drop w)  = factorWkPresTrans e e' w
factorWkPresTrans e  (ext🔒 f e')   (keep🔒 w) = factorWkPresTrans e e' w

factorExtPresTrans : ∀ (e : CExt Δ Γ ΓR) (e' : CExt Θ Δ ΔR) (w : Θ ⊆ Θ') → subst₂ (CExt Θ') (lCtxPresTrans e e' w) (rCtxPresTrans e e' w) (factorExt (extRAssoc e e') w) ≡ extRAssoc (factorExt e (factorWk e' w)) (factorExt e' w)
factorExtPresTrans _e _e' _w = ExtIsProp _ _


-- Special case of factorWk

rCtx′ : (e : CExt Γ ΓL ΓR) → (e' : LFExt Γ' Γ ΓR') → Ctx
rCtx′ {ΓR' = []}       e         nil      = []
rCtx′ {ΓR' = ΓR' `, a} nil       (ext e') = ΓR' `, a
rCtx′ {ΓR' = ΓR' `, _} (ext e)   (ext e') = rCtx′ {ΓR' = ΓR'} (ext e) e'
rCtx′ {ΓR' = ΓR' `, _} (ext🔒- e) (ext e') = rCtx′ {ΓR' = ΓR'} (ext🔒- e) e'

-- Special case of factorWk where the second argument consists of only drops (simulated using LFExt)
factorDropsWk : (e : CExt Γ ΓL ΓR) → (e' : LFExt Γ' Γ ΓR') → LFExt (lCtx e (LFExtTo⊆ e')) ΓL (rCtx′ e e')
factorDropsWk {ΓR' = []}       e         nil      = subst (λ ΓL → LFExt (lCtx e idWk) ΓL _) (lCtxPresId e) nil
factorDropsWk {ΓR' = ΓR'}      nil       (ext e') = (ext e')
factorDropsWk {ΓR' = ΓR' `, _} (ext e)   (ext e') = factorDropsWk {ΓR' = ΓR'} (ext e) e'
factorDropsWk {ΓR' = ΓR' `, _} (ext🔒- e) (ext e') = factorDropsWk {ΓR' = ΓR'} (ext🔒- e) e'

-- factorDropsWk is indeed a special case of factorWk
factorDropsWkIsfactorWk : (e : CExt Γ ΓL ΓR) → (e' : LFExt Γ' Γ ΓR') → LFExtTo⊆ (factorDropsWk e e') ≡ factorWk e (LFExtTo⊆ e')
factorDropsWkIsfactorWk nil       nil      = refl
factorDropsWkIsfactorWk nil       (ext e') = refl
factorDropsWkIsfactorWk (ext e)   nil      = factorDropsWkIsfactorWk e nil
factorDropsWkIsfactorWk (ext e)   (ext e') = factorDropsWkIsfactorWk (ext e) e'
factorDropsWkIsfactorWk (ext🔒- e) nil      = factorDropsWkIsfactorWk e nil
factorDropsWkIsfactorWk (ext🔒- e) (ext e') = factorDropsWkIsfactorWk (ext🔒- e) e'

-- Note: factorDropsExt is not need as it has the same type as factorDrops and ExtIsProp

factorisationLemma : (e : LFExt Γ ΓL ΓR) → (w : Γ ⊆ Γ')
  → LFExtTo⊆ e ∙ w ≡ factorWk e w ∙ LFExtTo⊆ (factorExt e w)
factorisationLemma nil    w = trans (leftIdWk _) (sym (rightIdWk _))
factorisationLemma (ext e) (drop w) = cong drop (factorisationLemma (ext e) w)
factorisationLemma (ext e) (keep w) = cong drop (factorisationLemma e w)

-- Properties about absorption of upLFExt

lCtxAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → lCtx {θ = ff} e w ≡ lCtx {θ = tt} (upLFExt e) w
lCtxAbsorbsUpLFExt nil      w       = refl
lCtxAbsorbsUpLFExt (ext e) (drop w) = lCtxAbsorbsUpLFExt (ext e) w
lCtxAbsorbsUpLFExt (ext e) (keep w) = lCtxAbsorbsUpLFExt e w

rCtxAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → rCtx {θ = ff} e w ≡ rCtx {θ = tt} (upLFExt e) w
rCtxAbsorbsUpLFExt nil      w       = refl
rCtxAbsorbsUpLFExt (ext e) (drop w) = cong (_`, _) (rCtxAbsorbsUpLFExt (ext e) w)
rCtxAbsorbsUpLFExt (ext e) (keep w) = cong (_`, _) (rCtxAbsorbsUpLFExt e w)

factorWkAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → subst (_ ⊆_) (lCtxAbsorbsUpLFExt e w) (factorWk e w) ≡ factorWk (upLFExt e) w
factorWkAbsorbsUpLFExt nil     w        = refl
factorWkAbsorbsUpLFExt (ext e) (drop w) = factorWkAbsorbsUpLFExt (ext e) w
factorWkAbsorbsUpLFExt (ext e) (keep w) = factorWkAbsorbsUpLFExt e w

factorExtAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → subst₂ (CExt _) (lCtxAbsorbsUpLFExt e w) (rCtxAbsorbsUpLFExt e w) (upLFExt (factorExt e w)) ≡ factorExt (upLFExt e) w
factorExtAbsorbsUpLFExt _ _ = ExtIsProp _ _
