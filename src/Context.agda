module Context (Ty : Set) where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; sym ; trans)

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
  θ : Flag

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
wᵣ : LFExt Γ ΓL ΓR → Γ ≤ ΓL
wᵣ nil     = idWk
wᵣ (ext e) = drop (wᵣ e)

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

-- "residual" extension
resExt : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ' ≤ Γ → LFExt Γ' ((←🔒 Γ') 🔒) (🔒→ Γ')
resExt e       (drop w)  = ext (resExt e w)
resExt nil     (keep🔒 w) = nil
resExt (ext e) (keep w)  = ext (resExt e w)

-- "stashed" weakening
stashWk : (e : LFExt Γ (ΓL 🔒) ΓR) → Γ' ≤ Γ → (←🔒 Γ') ≤ ΓL
stashWk e       (drop w)  = stashWk e w
stashWk nil     (keep🔒 w) = w
stashWk (ext e) (keep w)  = stashWk e w

-- the operation ←🔒 returns the context to the left of 🔒
←🔒IsPre🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓL ≡ (←🔒 Γ)
←🔒IsPre🔒 nil = refl
←🔒IsPre🔒 (ext e) = ←🔒IsPre🔒 e

-- the operation 🔒→ returns the context to the right of 🔒
🔒→isPost🔒 : LFExt Γ (ΓL 🔒) ΓR → ΓR ≡ (🔒→ Γ)
🔒→isPost🔒 nil     = refl
🔒→isPost🔒 (ext e) = cong (_`, _) (🔒→isPost🔒 e)

---------------
-- Slicing laws
---------------

resAccLem : (w' : Δ ≤ Γ') (w  : Γ' ≤ Γ) (e : LFExt Γ (ΓL 🔒) ΓR)
  → resExt (resExt e w) w' ≡ resExt e (w ∙ w')
resAccLem (drop w') (drop w)   nil     = cong ext (resAccLem w' (drop w) nil)
resAccLem (drop w') (drop w)   (ext e) = cong ext (resAccLem w' (drop w) (ext e))
resAccLem (drop w') (keep w)   (ext e) = cong ext (resAccLem w' (keep w) (ext e))
resAccLem (drop w') (keep🔒 w)  nil     = cong ext (resAccLem w' (keep🔒 w) nil)
resAccLem (keep w') (drop w)   nil     = cong ext (resAccLem w' w nil)
resAccLem (keep w') (drop w)   (ext e) = cong ext (resAccLem w' w (ext e))
resAccLem (keep w') (keep w)   (ext e) = cong ext (resAccLem w' w e)
resAccLem (keep🔒 w') (keep🔒 w) nil     = refl

stashSquash : (w' : Δ ≤ Γ') (w  : Γ' ≤ Γ) (e : LFExt Γ (ΓL 🔒) ΓR)
  → (stashWk e w ∙ stashWk (resExt e w) w') ≡ stashWk e (w ∙ w')
stashSquash (drop w')  (drop w)  nil     = stashSquash w' (drop w) nil
stashSquash (drop w')  (drop w)  (ext e) = stashSquash w' (drop w) (ext e)
stashSquash (keep w')  (drop w)  nil     = stashSquash w' w nil
stashSquash (keep w')  (drop w)  (ext e) = stashSquash w' w (ext e)
stashSquash (drop w')  (keep w)  (ext e) = stashSquash w' (keep w) (ext e)
stashSquash (keep w')  (keep w)  (ext e) = stashSquash w' w e
stashSquash (drop w')  (keep🔒 w) nil     = stashSquash w' (keep🔒 w) nil
stashSquash (keep🔒 w') (keep🔒 w) nil     = refl

-- a good slice is a slice whose composition doesn't change
goodSlice : (w : Γ' ≤ Γ) → (e : LFExt Γ (ΓL 🔒) ΓR)
  → wᵣ e ∙ w ≡ (keep🔒 (stashWk e w) ∙ wᵣ (resExt e w))
goodSlice (drop w)  nil     = cong drop (goodSlice w nil)
goodSlice (drop w)  (ext e) = cong drop (goodSlice w (ext e))
goodSlice (keep w)  (ext e) = cong drop (goodSlice w e)
goodSlice (keep🔒 w) nil     = cong keep🔒 (trans (leftIdWk w) (sym (rightIdWk w)))

stashWkId : (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → stashWk e idWk ≡ idWk
stashWkId {Γ `, x} (ext e) = stashWkId e
stashWkId {Γ 🔒}    nil     = refl

resExtId :  (e : LFExt Γ (←🔒 Γ 🔒) (🔒→ Γ)) → resExt e idWk ≡ e
resExtId {Γ `, x} (ext e) = cong ext (resExtId e)
resExtId {Γ 🔒}    nil     = refl
