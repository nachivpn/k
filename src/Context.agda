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

module carlostome/k/src/IS4/Term-agda where

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

    factor1 : Γ R Δ → Γ' ⊆ Γ → ∃ λ Δ' → Δ' ⊆ Δ × Γ' R Δ'
    factor1 nil⊑           Γ'≤Γ
      = _ , Γ'≤Γ , nil⊑
    factor1 (ext⊑ Γ⊑Δ)     Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
    ... | Δ' , Δ'≤Δ , Γ'⊑Δ'
      = Δ' , drop Δ'≤Δ , Γ'⊑Δ'
    factor1 (ext🔒⊑ _ Γ⊑Δ) Γ'≤Γ with factor1 (_ , Γ⊑Δ) Γ'≤Γ
    ... | Δ' , Δ'≤Δ , Γ'⊑Δ'
      = (Δ' 🔒) , keep🔒 Δ'≤Δ , ⊑-trans Γ'⊑Δ' (ext🔒⊑ tt extRId)

    factor2 : Γ R Δ → Δ ⊆ Δ' → ∃ λ Γ' → Γ ⊆ Γ' × Γ' R Δ'
    factor2 nil⊑           Δ≤Δ'
      = _ , Δ≤Δ' , nil⊑
    factor2 (ext⊑ Γ⊑Δ)     Δ≤Δ'
      = factor2 (_ , Γ⊑Δ) (fresh ∙ Δ≤Δ')
    factor2 (ext🔒⊑ _ Γ⊑Δ) Δ≤Δ' with factor2 (_ , Γ⊑Δ) (sliceLeft extRId Δ≤Δ')
    ... | Γ' , Γ≤Γ' , Γ'⊑Δ'
      = Γ' , Γ≤Γ' , ⊑-trans Γ'⊑Δ' (⊑-trans (ext🔒⊑ tt extRId) (_ , upLFExt (wkLFExt extRId Δ≤Δ')))

-- f1LRCtx e w == proj₁ (factor1 (_ , e) w)
f1LRCtx : CExt Δ Γ ΓR → Γ' ⊆ Γ → Ctx
f1LRCtx {Γ' = Γ'} nil       w = Γ'
f1LRCtx {Γ' = Γ'} (ext e)   w = f1LRCtx e w
f1LRCtx {Γ' = Γ'} (ext🔒- e) w = (f1LRCtx e w) 🔒

-- f1RCtx e w == proj₁ (proj₂ (proj₂ (factor1 (_ , e) w)))
f1RCtx : CExt Δ Γ ΓR → Γ' ⊆ Γ → Ctx
f1RCtx nil       w = []
f1RCtx (ext e)   w = f1RCtx e w
f1RCtx (ext🔒- e) w = (f1RCtx e w) 🔒

--
factor1Ext : (e : CExt Δ Γ ΓR) → (w : Γ' ⊆ Γ) → CExt (f1LRCtx e w) Γ' (f1RCtx e w)
factor1Ext nil        w = nil
factor1Ext (ext e)    w = factor1Ext e w
factor1Ext (ext🔒- e) w = ext🔒- (factor1Ext e w)

--
factor1≤ : (e : CExt Δ Γ ΓR) → (w : Γ' ⊆ Γ) → (f1LRCtx e w) ⊆ Δ
factor1≤ nil        w = w
factor1≤ (ext e)    w = drop (factor1≤ e w)
factor1≤ (ext🔒- e) w = keep🔒 (factor1≤ e w)

-- f2LCtx e w == proj₁ (factor2 (_ , e) w)
f2LCtx : CExt Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
f2LCtx {Γ = Γ}      {Γ' = Γ'}       nil        w
  = Γ'
f2LCtx {Γ = Γ `, a} {Γ' = Γ' `, b}  (ext e)    (drop w)
  = f2LCtx (ext e) w
f2LCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)    (keep w)
  = f2LCtx e w
f2LCtx {Γ = Γ 🔒} {Γ' = Γ' `, a}     (ext🔒- e) (drop w)
  = f2LCtx  (ext🔒- e) w
f2LCtx {Γ = Γ 🔒} {Γ' = Γ' 🔒}        (ext🔒- e) (keep🔒 w)
  = f2LCtx e w

-- f2LCtx e w == proj₁ (proj₂ (proj₂ (factor2 (_ , e) w)))
f2RCtx : CExt Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
f2RCtx  {Γ = Γ}     {Γ' = Γ'}      nil       w
  = []
f2RCtx {Γ = Γ `, a} {Γ' = Γ' `, b} (ext e)   (drop w)
  = f2RCtx (ext e) w `, b
f2RCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)  (keep w)
  = f2RCtx e w `, a
f2RCtx {Γ = Γ 🔒}    {Γ' = Γ' `, a} (ext🔒- e) (drop  {a = a} w)
  = f2RCtx (ext🔒- e) w `, a
f2RCtx {Γ = Γ 🔒}    {Γ' = Γ' 🔒}    (ext🔒- e) (keep🔒 w)
  = (f2RCtx e w) 🔒

--
factor2Ext : (e : CExt Γ ΓL ΓR) → (w : Γ ⊆ Γ') → CExt Γ' (f2LCtx e w) (f2RCtx e w)
factor2Ext nil       w         = nil
factor2Ext (ext e)   (drop w)  = ext (factor2Ext (ext e) w)
factor2Ext (ext  e)  (keep w)  = ext (factor2Ext e w)
factor2Ext (ext🔒- e) (drop w)  = ext (factor2Ext (ext🔒- e) w)
factor2Ext (ext🔒- e) (keep🔒 w) = ext🔒- (factor2Ext e w)

--
factor2≤ : (e : CExt Γ ΓL ΓR) → (w : Γ ⊆ Γ') → ΓL ⊆ (f2LCtx e w)
factor2≤ nil       w         = w
factor2≤ (ext e)   (drop w)  = factor2≤ (ext e) w
factor2≤ (ext e)   (keep w)  = factor2≤ e w
factor2≤ (ext🔒- e) (drop w)  = factor2≤ (ext🔒- e) w
factor2≤ (ext🔒- e) (keep🔒 w) = factor2≤ e w

--------------------------------------------
-- Factorisation laws for general extensions
--------------------------------------------

f2LCtxPresId : (e : CExt Γ ΓL ΓR) → f2LCtx e idWk ≡ ΓL
f2LCtxPresId nil       = refl
f2LCtxPresId (ext e)   = f2LCtxPresId e
f2LCtxPresId (ext🔒- e) = f2LCtxPresId e

f2RCtxPresId : (e : CExt Γ ΓL ΓR) → f2RCtx e idWk ≡ ΓR
f2RCtxPresId nil       = refl
f2RCtxPresId (ext e)   = cong (_`, _) (f2RCtxPresId e)
f2RCtxPresId (ext🔒- e) = cong _🔒 (f2RCtxPresId e)

factor2≤PresId : (e : CExt Γ ΓL ΓR) → subst (ΓL ⊆_) (f2LCtxPresId e) (factor2≤ e idWk) ≡ idWk[ ΓL ]
factor2≤PresId nil       = refl
factor2≤PresId (ext e)   = factor2≤PresId e
factor2≤PresId (ext🔒- e) = factor2≤PresId e

factor2ExtPresId : (e : CExt Γ ΓL ΓR) → subst₂ (CExt Γ) (f2LCtxPresId e) (f2RCtxPresId e) (factor2Ext e idWk) ≡ e
factor2ExtPresId _ = ExtIsProp _ _

f2LCtxPres∙ : (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → f2LCtx e (w ∙ w') ≡ f2LCtx (factor2Ext e w) w'
f2LCtxPres∙ nil         w           w'         = refl
f2LCtxPres∙ e@(ext _)   w@(drop _)  (drop w')  = f2LCtxPres∙ e w w'
f2LCtxPres∙ e@(ext _)   w@(keep _)  (drop w')  = f2LCtxPres∙ e w w'
f2LCtxPres∙ e@(ext🔒- _) w@(drop _)  (drop w')  = f2LCtxPres∙ e w w'
f2LCtxPres∙ e@(ext🔒- _) w@(keep🔒 _) (drop w')  = f2LCtxPres∙ e w w'
f2LCtxPres∙ e@(ext _)   (drop w)    (keep w')  = f2LCtxPres∙ e w w'
f2LCtxPres∙ e@(ext🔒- _) (drop w)    (keep w')  = f2LCtxPres∙ e w w'
f2LCtxPres∙ (ext e)     (keep w)    (keep w')  = f2LCtxPres∙ e w w'
f2LCtxPres∙ (ext🔒- e)   (keep🔒 w)   (keep🔒 w') = f2LCtxPres∙ e w w'

f2RCtxPres∙ : (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → f2RCtx e (w ∙ w') ≡ f2RCtx (factor2Ext e w) w'
f2RCtxPres∙ nil         w           w'         = refl
f2RCtxPres∙ e@(ext _)   w@(drop _)  (drop w')  = cong (_`, _) (f2RCtxPres∙ e w w')
f2RCtxPres∙ e@(ext _)   w@(keep _)  (drop w')  = cong (_`, _) (f2RCtxPres∙ e w w')
f2RCtxPres∙ e@(ext🔒- _) w@(drop _)  (drop w')  = cong (_`, _) (f2RCtxPres∙ e w w')
f2RCtxPres∙ e@(ext🔒- _) w@(keep🔒 _) (drop w')  = cong (_`, _) (f2RCtxPres∙ e w w')
f2RCtxPres∙ e@(ext _)   (drop w)    (keep w')  = cong (_`, _) (f2RCtxPres∙ e w w')
f2RCtxPres∙ e@(ext🔒- _) (drop w)    (keep w')  = cong (_`, _) (f2RCtxPres∙ e w w')
f2RCtxPres∙ (ext e)     (keep w)    (keep w')  = cong (_`, _) (f2RCtxPres∙ e w w')
f2RCtxPres∙ (ext🔒- e)   (keep🔒 w)   (keep🔒 w') = cong _🔒 (f2RCtxPres∙ e w w')

factor2≤Pres∙ : ∀ (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → subst (ΓL ⊆_) (f2LCtxPres∙ e w w') (factor2≤ e (w ∙ w')) ≡ factor2≤ e w ∙ factor2≤ (factor2Ext e w) w'
factor2≤Pres∙ nil         w           w'         = refl
factor2≤Pres∙ e@(ext _)   w@(drop _)  (drop w')  = factor2≤Pres∙ e w w'
factor2≤Pres∙ e@(ext _)   w@(keep _)  (drop w')  = factor2≤Pres∙ e w w'
factor2≤Pres∙ e@(ext🔒- _) w@(drop _)  (drop w')  = factor2≤Pres∙ e w w'
factor2≤Pres∙ e@(ext🔒- _) w@(keep🔒 _) (drop w')  = factor2≤Pres∙ e w w'
factor2≤Pres∙ e@(ext _)   (drop w)    (keep w')  = factor2≤Pres∙ e w w'
factor2≤Pres∙ e@(ext🔒- _) (drop w)    (keep w')  = factor2≤Pres∙ e w w'
factor2≤Pres∙ (ext e)     (keep w)    (keep w')  = factor2≤Pres∙ e w w'
factor2≤Pres∙ (ext🔒- e)   (keep🔒 w)   (keep🔒 w') = factor2≤Pres∙ e w w'

factor2ExtPres∙ : ∀ (e : CExt Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → subst₂ (CExt Γ'') (f2LCtxPres∙ e w w') (f2RCtxPres∙ e w w') (factor2Ext e (w ∙ w')) ≡ factor2Ext (factor2Ext e w) w'
factor2ExtPres∙ _ _ _ = ExtIsProp _ _

----------------
-- Substitutions
----------------

module Substitution
  (Tm          : (Γ : Ctx) → (a : Ty) → Set)
  (var         : {Γ : Ctx} → {a : Ty} → (v : Var Γ a) → Tm Γ a)
  (wkTm        : {Γ' Γ : Ctx} → {a : Ty} → (w : Γ ⊆ Γ') → (t : Tm Γ a) → Tm Γ' a)
  (Acc         : (Δ Γ ΓR : Ctx) → Set)
  {newR        : (Γ : Ctx) → Ctx}
  (new         : ∀ {Γ : Ctx} → Acc (Γ 🔒) Γ (newR Γ))
  (f2LCtx      : {Δ Γ ΓR Δ' : Ctx} → (e : Acc Δ Γ ΓR) → (w : Δ ⊆ Δ') → Ctx)
  (factor2≤    : ∀ {Δ Γ ΓR Δ' : Ctx} (e : Acc Δ Γ ΓR) (w : Δ ⊆ Δ') → Γ ⊆ f2LCtx e w)
  (f2RCtx      : {Δ Γ ΓR Δ' : Ctx} → (e : Acc Δ Γ ΓR) → (w : Δ ⊆ Δ') → Ctx)
  (factor2Ext  : ∀ {Δ Γ ΓR Δ' : Ctx} (e : Acc Δ Γ ΓR) (w : Δ ⊆ Δ') → Acc Δ' (f2LCtx e w) (f2RCtx e w))
  where

  data Sub : Ctx → Ctx → Set where
    []   : Sub Δ []
    _`,_ : (σ : Sub Δ Γ) → (t : Tm Δ a) → Sub Δ (Γ `, a)
    lock : (σ : Sub ΔL Γ) → (e : Acc Δ ΔL ΔR) → Sub Δ (Γ 🔒)

  variable
    σ σ' σ'' : Sub Δ Γ
    τ τ' τ'' : Sub Δ Γ

  -- weaken a substitution, composition operation for weakening before substitution
  wkSub : Γ ⊆ Γ' → Sub Γ Δ → Sub Γ' Δ
  wkSub w []         = []
  wkSub w (s `, t)   = wkSub w s `, wkTm w t
  wkSub w (lock s e) = lock (wkSub (factor2≤ e w) s) (factor2Ext e w)

  -- composition operation for weakening after substitution
  trimSub : Δ ⊆ Γ → Sub Γ' Γ → Sub Γ' Δ
  trimSub base      []         = []
  trimSub (drop w)  (s `, t)   = trimSub w s
  trimSub (keep w)  (s `, t)   = trimSub w s `, t
  trimSub (keep🔒 w) (lock s e) = lock (trimSub w s) e

  -- "drop" the last variable in the context
  dropₛ : Sub Γ Δ → Sub (Γ `, a) Δ
  dropₛ s = wkSub fresh s

  -- "keep" the last variable in the context
  keepₛ : Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
  keepₛ s = dropₛ s `, var ze

  -- "keep" the lock in the context
  keep🔒ₛ : Sub Γ Δ → Sub (Γ 🔒) (Δ 🔒)
  keep🔒ₛ s = lock s new

  -- embed a weakening to substitution
  embWk : Δ ⊆ Γ → Sub Γ Δ
  embWk base      = []
  embWk (drop w)  = dropₛ (embWk w)
  embWk (keep w)  = keepₛ (embWk w)
  embWk (keep🔒 w) = keep🔒ₛ (embWk w)

  -- identity substitution
  idₛ : Sub Γ Γ
  idₛ = embWk idWk

  idₛ[_] = λ Γ → idₛ {Γ}

  ExtToSub : (e : Acc Δ Γ ΓR) → Sub Δ (Γ 🔒)
  ExtToSub e = lock idₛ e

  -- apply substitution to a variable
  substVar : Sub Γ Δ → Var Δ a → Tm Γ a
  substVar (s `, t) ze     = t
  substVar (s `, t) (su v) = substVar s v

  module Composition
    (substTm     : {Δ Γ : Ctx} → {a : Ty} → (σ : Sub Δ Γ) → (t : Tm Γ a) → Tm Δ a)
    (f2LCtxₛ     : {Δ Γ ΓR Θ : Ctx} → (e : Acc Δ Γ ΓR) → (σ : Sub Θ Δ) → Ctx)
    (factor2Sub  : ∀ {Δ Γ ΓR Θ : Ctx} (e : Acc Δ Γ ΓR) (σ : Sub Θ Δ) → Sub (f2LCtxₛ e σ) Γ)
    (f2RCtxₛ     : {Δ Γ ΓR Θ : Ctx} → (e : Acc Δ Γ ΓR) → (σ : Sub Θ Δ) → Ctx)
    (factor2Extₛ : ∀ {Δ Γ ΓR Θ : Ctx} (e : Acc Δ Γ ΓR) (σ : Sub Θ Δ) → Acc Θ (f2LCtxₛ e σ) (f2RCtxₛ e σ))
    where

    infixr 20 _∙ₛ_

    -- substitution composition
    _∙ₛ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
    []        ∙ₛ s = []
    (s' `, t) ∙ₛ s = s' ∙ₛ s `, substTm s t
    lock s' e ∙ₛ s = lock (s' ∙ₛ factor2Sub e s) (factor2Extₛ e s)
