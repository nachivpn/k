{-# OPTIONS --safe --without-K #-}
module Context.Base (Ty : Set) where

open import Data.Empty   using (⊥ ; ⊥-elim)
open import Data.Product using (Σ ; _×_ ; _,_ ; ∃ ; ∃₂ ; proj₂)
open import Data.Unit    using (⊤ ; tt)

open import Relation.Binary.Definitions using (Reflexive ; Transitive)

private
  variable
    a b c d : Ty

infixl 6 _# _`,_
infix  5 _⊆_
infixl 5 _,,_

-----------
-- Contexts
-----------

data Ctx : Set where
  []   : Ctx
  _`,_ : (Γ : Ctx) → (a : Ty) → Ctx
  _#   : (Γ : Ctx) → Ctx            -- a lock 🔒

[#] : Ctx
[#] = [] #

[_] : Ty → Ctx
[_] a = [] `, a

variable
  Γ Γ' Γ'' ΓL ΓL' ΓL'' ΓLL ΓLR ΓR ΓR' ΓR'' ΓRL ΓRR : Ctx
  Δ Δ' Δ'' ΔL ΔL' ΔL'' ΔLL ΔLR ΔR ΔR' ΔR'' ΔRL ΔRR : Ctx
  Θ Θ' Θ'' ΘL ΘL' ΘL'' ΘLL ΘLR ΘR ΘR' ΘR'' ΘRL ΘRR : Ctx
  Ξ Ξ' Ξ'' ΞL ΞL' ΞL'' ΞLL ΞLR ΞR ΞR' ΞR'' ΞRL ΞRR : Ctx

-- append contexts (++)
_,,_ : Ctx → Ctx → Ctx
Γ ,, []       = Γ
Γ ,, (Δ `, x) = (Γ ,, Δ) `, x
Γ ,, (Δ #)    = (Γ ,, Δ) #

-- contexts free of locks
#-free : Ctx → Set
#-free []        = ⊤
#-free (Γ `, _a) = #-free Γ
#-free (_Γ #)    = ⊥

-- context to left of the last lock
←# : Ctx → Ctx
←# []        = []
←# (Γ `, _a) = ←# Γ
←# (Γ #)     = Γ

-- context to the right of the last lock
#→ : Ctx → Ctx
#→ []       = []
#→ (Γ `, a) = #→ Γ `, a
#→ (_Γ #)   = []

-------------
-- Weakenings
-------------

-- weakening relation
data _⊆_  : Ctx → Ctx → Set where
  base   : [] ⊆ []
  drop   : (w : Γ ⊆ Δ) → Γ ⊆ Δ `, a
  keep   : (w : Γ ⊆ Δ) → Γ `, a ⊆ Δ `, a
  keep#  : (w : Γ ⊆ Δ) → Γ # ⊆ Δ #

{-
  Notes on _⊆_:

  In addition to the regular definition of weakening (`base`, `drop` and `keep`),
  we also allow weakening in the presence of locks:

  - `keep#` allows weakening under locks

  Disallowing weakening with locks in general ensures that values
  that depend on "local" assumptions cannot be boxed by simply
  weakening with locks.

-}

pattern drop[_] a w = drop {a = a} w
pattern keep[_] a w = keep {a = a} w

variable
  w w' w'' : Γ ⊆ Γ'

-- weakening is reflexive
idWk[_] : (Γ : Ctx) → Γ ⊆ Γ
idWk[_] []        = base
idWk[_] (Γ `, _a) = keep  idWk[ Γ ]
idWk[_] (Γ #)     = keep# idWk[ Γ ]

idWk = λ {Γ} → idWk[ Γ ]

-- weakening is transitive (or can be composed)
_∙_ : Θ ⊆ Δ → Δ ⊆ Γ → Θ ⊆ Γ
w       ∙ base     = w
w       ∙ drop  w' = drop  (w ∙ w')
drop  w ∙ keep  w' = drop  (w ∙ w')
keep  w ∙ keep  w' = keep  (w ∙ w')
keep# w ∙ keep# w' = keep# (w ∙ w')

-- weakening that "generates a fresh variable"
fresh : Γ ⊆ Γ `, a
fresh = drop idWk

fresh[_] = λ {Γ} a → fresh {Γ} {a}

------------
-- Variables
------------

data Var : Ctx → Ty → Set where
  zero : Var (Γ `, a) a
  succ : (v : Var Γ a) → Var (Γ `, b) a

pattern v0 = zero
pattern v1 = succ v0
pattern v2 = succ v1

wkVar : Γ ⊆ Γ' → Var Γ a → Var Γ' a
wkVar (drop e) v        = succ (wkVar e v)
wkVar (keep e) zero     = zero
wkVar (keep e) (succ v) = succ (wkVar e v)

-- OBS: in general, Γ ⊈ Δ ,, Γ
leftWkVar : (v : Var Γ a) → Var (Δ ,, Γ) a
leftWkVar zero     = zero
leftWkVar (succ v) = succ (leftWkVar v)

--------------------
-- Context extension
--------------------

-- The three-place relation Ext θ relates contexts Γ, ΓL, and ΓR
-- exactly when Γ = ΓL ,, ΓR (cf. lemmas extIs,, and ,,IsExt
-- below). In other words, Ext θ is the graph of context concatenation
-- _,,_. The relation Ext θ Γ ΓL ΓR may be read as "Γ is ΓL extended
-- to the right with ΓR".
--
-- The flag θ specifies whether the context ΓR we are extending with
-- may contain locks (if set to tt) or not (if set to ff).
--
-- Ext is used below to define lock-free and arbitrary context
-- extensions LFExt and CExt, respectively, in a uniform way. The
-- relations LFExt and CExt in turn are used to define the modal
-- accessibility premises of the unbox term formers for λ_IK (see data
-- Tm in IK.Term.Base) and λ_IS4 (see data Tm in IS4.Term.Base),
-- respectively, in a uniform way.

data Flag : Set where
  tt ff : Flag

variable
  θ θ' : Flag

-- with locks?
WL : Flag → Set
WL tt = ⊤
WL ff = ⊥

data Ext (θ : Flag) : Ctx → Ctx → Ctx → Set where
  nil  : Ext θ Γ Γ []
  ext  : (e : Ext θ Γ ΓL ΓR) → Ext θ (Γ `, a) ΓL (ΓR `, a)
  ext# : WL θ → (e : Ext θ Γ ΓL ΓR) → Ext θ (Γ #) ΓL (ΓR #)

pattern nil[_] Γ   = nil  {Γ = Γ}
pattern ext[_] a e = ext  {a = a} e
pattern ext#-    e = ext# tt      e

-- Lock-free context extension (w/o locks, Ext flag set to ff)
--
-- The modal accessibility relation _◁_ for λ_IK defined in Figure 4
-- in the paper can equivalently be defined by Δ ◁ Γ = ∃ ΔR. LFExt Γ
-- (Δ #) ΔR.
--
-- Lock-free context extensions are also used to represent sequences
-- w : Γ ⊆ Γ `, a₁ `, … `, aₙ of drops in the "shift-unbox" conversion
-- rule unbox t (w · e) ≈ unbox (wkTm w t) e (cf. discussion below
-- Theorem 7 in the paper).
LFExt : Ctx → Ctx → Ctx → Set
LFExt = Ext ff

_◁IK_ = λ Δ Γ → Σ Ctx λ ΔR → LFExt Γ (Δ #) ΔR

-- Arbitrary context extension (possibly w/ locks, Ext flag set to tt)
--
-- The modal accessibility relation _◁_ for λ_IS4 defined in Figure 10
-- in the paper can equivalently be defined by Δ ◁ Γ = ∃ ΔR. CExt Γ Δ
-- ΔR.
CExt : Ctx → Ctx → Ctx → Set
CExt = Ext tt

_◁IS4_ = λ Δ Γ → Σ Ctx λ ΔR → CExt Γ Δ ΔR

pattern nil◁    = _ , nil
pattern ext◁  e = _ , ext     e
pattern ext#◁ e = _ , ext# tt e

-- extension that "generates a new context frame"
pattern new◁IK  = _ , nil
pattern new◁IS4 = _ , ext# tt nil

variable
  e e' e'' : Ext θ Γ ΓL ΓR

-- embed lock-free extensions into ones that extend with locks
upLFExt : LFExt Γ ΓL ΓR → Ext θ Γ ΓL ΓR
upLFExt nil     = nil
upLFExt (ext e) = ext (upLFExt e)

-- left identity of extension
extLId : CExt Γ [] Γ
extLId {Γ = []}       = nil
extLId {Γ = _Γ `, _a} = ext     extLId
extLId {Γ = _Γ #}     = ext# tt extLId

-- right identity of extension
extRId : Ext θ Γ Γ []
extRId = nil

-- extension that "generates a fresh variable"
freshExt : Ext θ (Γ `, a) Γ ([] `, a)
freshExt = ext nil

freshExt[_] = λ {θ} {Γ} a → freshExt {θ} {Γ} {a}

-- lock-free extensions yield a "right" weakening (i.e., adding variables on the right)
LFExtToWk : LFExt Γ ΓL ΓR → ΓL ⊆ Γ
LFExtToWk nil     = idWk
LFExtToWk (ext e) = drop (LFExtToWk e)

-- extension is assocative
extRAssoc : Ext θ ΓL ΓLL ΓLR → Ext θ Γ ΓL ΓR → Ext θ Γ ΓLL (ΓLR ,, ΓR)
extRAssoc el nil         = el
extRAssoc el (ext    er) = ext    (extRAssoc el er)
extRAssoc el (ext# x er) = ext# x (extRAssoc el er)

_∙Ext_ = extRAssoc

-------------------------------------
-- Operations on lock-free extensions
-------------------------------------

-- weaken the extension of a context
wkLFExt : (e : LFExt Γ (ΓL #) ΓR) → (w : Γ ⊆ Γ') → LFExt Γ' ((←# Γ') #) (#→ Γ')
wkLFExt e       (drop  w) = ext (wkLFExt e w)
wkLFExt nil     (keep# w) = nil
wkLFExt (ext e) (keep  w) = ext (wkLFExt e w)

-- left weaken the (lock-free) extension of a context
leftWkLFExt : (e : LFExt Γ ΓL ΓR) → LFExt (Δ ,, Γ) (Δ ,, ΓL) ΓR
leftWkLFExt nil     = nil
leftWkLFExt (ext e) = ext (leftWkLFExt e)

-- slice a weakening to the left of a lock
sliceLeft : (e : LFExt Γ (ΓL #) ΓR) → (w : Γ ⊆ Γ') → ΓL ⊆ ←# Γ'
sliceLeft e       (drop  w) = sliceLeft e w
sliceLeft (ext e) (keep  w) = sliceLeft e w
sliceLeft nil     (keep# w) = w

-- slice a weakening to the right of a lock
sliceRight : (e : LFExt Γ (ΓL #) ΓR) → (w : Γ ⊆ Γ') → ←# Γ' # ⊆ Γ'
sliceRight e w = LFExtToWk (wkLFExt e w)

-----------------------------------
-- Operations on general extensions
-----------------------------------

◁IS4-refl : Reflexive _◁IS4_
◁IS4-refl = nil◁

◁IS4-trans : Transitive _◁IS4_
◁IS4-trans (_ , Γ◁Δ) (_ , Δ◁Ε) = _ , extRAssoc Γ◁Δ Δ◁Ε

private
  -- we don't use factor1 anymore
  factor1 : Γ ◁IS4 Δ → Γ' ⊆ Γ → ∃ λ Δ' → Δ' ⊆ Δ × Γ' ◁IS4 Δ'
  factor1 nil◁        Γ'⊆Γ
    = _ , Γ'⊆Γ , nil◁
  factor1 (ext◁  Γ◁Δ) Γ'⊆Γ with factor1 (_ , Γ◁Δ) Γ'⊆Γ
  ... | Δ' , Δ'⊆Δ , Γ'◁Δ'
    = Δ' , drop Δ'⊆Δ , Γ'◁Δ'
  factor1 (ext#◁ Γ◁Δ) Γ'⊆Γ with factor1 (_ , Γ◁Δ) Γ'⊆Γ
  ... | Δ' , Δ'⊆Δ , Γ'◁Δ'
    = Δ' # , keep# Δ'⊆Δ , ◁IS4-trans Γ'◁Δ' (ext#◁ extRId)

  -- not used directly, but serves as a specification of
  -- what is expected from factorExt and factorWk
  factor2 : Γ ◁IS4 Δ → Δ ⊆ Δ' → ∃ λ Γ' → Γ ⊆ Γ' × Γ' ◁IS4 Δ'
  factor2 nil◁        Δ⊆Δ'
    = _ , Δ⊆Δ' , nil◁
  factor2 (ext◁  Γ◁Δ) Δ⊆Δ'
    = factor2 (_ , Γ◁Δ) (fresh ∙ Δ⊆Δ')
  factor2 (ext#◁ Γ◁Δ) Δ⊆Δ' with factor2 (_ , Γ◁Δ) (sliceLeft extRId Δ⊆Δ')
  ... | Γ' , Γ⊆Γ' , Γ'◁Δ'
    = Γ' , Γ⊆Γ' , ◁IS4-trans Γ'◁Δ' (◁IS4-trans (ext#◁ extRId) (_ , upLFExt (wkLFExt extRId Δ⊆Δ')))

-- "Left" context of factoring (see type of factorWk and factorExt)
-- lCtx e w == proj₁ (factor2 (_ , e) w)
lCtx : Ext θ Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
lCtx {Γ = Γ}      {Γ' = Γ'}       nil        w
  = Γ'
lCtx {Γ = Γ `, a} {Γ' = Γ' `, b}  (ext e)    (drop w)
  = lCtx (ext e) w
lCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)    (keep w)
  = lCtx e w
lCtx {Γ = Γ #} {Γ' = Γ' `, a}     (ext# f e) (drop w)
  = lCtx  (ext# f e) w
lCtx {Γ = Γ #} {Γ' = Γ' #}        (ext# f e) (keep# w)
  = lCtx e w

-- factorWk e w == proj₁ (proj₂ (factor2 (_ , e) w))
factorWk : (e : Ext θ Γ ΓL ΓR) → (w : Γ ⊆ Γ') → ΓL ⊆ lCtx e w
factorWk nil        w         = w
factorWk (ext e)    (drop w)  = factorWk (ext e) w
factorWk (ext e)    (keep w)  = factorWk e w
factorWk (ext# f e) (drop w)  = factorWk (ext# f e) w
factorWk (ext# f e) (keep# w) = factorWk e w

-- "Right" context of factoring (see type of factorExt)
-- rCtx e w == proj₁ (proj₂ (proj₂ (factor2 (_ , e) w)))
rCtx : Ext θ Γ ΓL ΓR → Γ ⊆ Γ' → Ctx
rCtx  {Γ = Γ}     {Γ' = Γ'}       nil        w
  = []
rCtx {Γ = Γ `, a} {Γ' = Γ' `, b}  (ext e)    (drop w)
  = rCtx (ext e) w `, b
rCtx {Γ = Γ `, a} {Γ' = Γ' `, .a} (ext e)    (keep w)
  = rCtx e w `, a
rCtx {Γ = Γ #}    {Γ' = Γ' `, a}  (ext# f e) (drop {a = a} w)
  = rCtx (ext# f e) w `, a
rCtx {Γ = Γ #}    {Γ' = Γ' #}     (ext# f e) (keep# w)
  = (rCtx e w) #

-- factorExt e w == proj₂ (proj₂ (proj₂ (factor2 (_ , e) w)))
factorExt : (e : Ext θ Γ ΓL ΓR) → (w : Γ ⊆ Γ') → Ext θ Γ' (lCtx e w) (rCtx e w)
factorExt nil        w         = nil
factorExt (ext    e) (drop w)  = ext    (factorExt (ext    e) w)
factorExt (ext    e) (keep w)  = ext    (factorExt e          w)
factorExt (ext# f e) (drop w)  = ext    (factorExt (ext# f e) w)
factorExt (ext# f e) (keep# w) = ext# f (factorExt e          w)

-------------------------------------------------------------------------------------
-- Substitutions (parameterized by terms `Tm` and modal accessibility relation `Acc`)
-------------------------------------------------------------------------------------

module Substitution
  (Tm          : (Γ : Ctx) → (a : Ty) → Set)
  (var         : {Γ : Ctx} → {a : Ty} → (v : Var Γ a) → Tm Γ a)
  (wkTm        : {Γ' Γ : Ctx} → {a : Ty} → (w : Γ ⊆ Γ') → (t : Tm Γ a) → Tm Γ' a)
  (Acc         : (Δ Γ ΓR : Ctx) → Set)
  {newR        : (Γ : Ctx) → Ctx}
  (new         : ∀ {Γ : Ctx} → Acc (Γ #) Γ (newR Γ))
  (lCtx        : {Δ Γ ΓR Δ' : Ctx} → (e : Acc Δ Γ ΓR) → (w : Δ ⊆ Δ') → Ctx)
  (factorWk    : ∀ {Δ Γ ΓR Δ' : Ctx} (e : Acc Δ Γ ΓR) (w : Δ ⊆ Δ') → Γ ⊆ lCtx e w)
  (rCtx        : {Δ Γ ΓR Δ' : Ctx} → (e : Acc Δ Γ ΓR) → (w : Δ ⊆ Δ') → Ctx)
  (factorExt   : ∀ {Δ Γ ΓR Δ' : Ctx} (e : Acc Δ Γ ΓR) (w : Δ ⊆ Δ') → Acc Δ' (lCtx e w) (rCtx e w))
  where

  data Sub : Ctx → Ctx → Set where
    []   : Sub Δ []
    _`,_ : (σ : Sub Δ  Γ) → (t : Tm Δ a)      → Sub Δ (Γ `, a)
    lock : (σ : Sub ΔL Γ) → (e : Acc Δ ΔL ΔR) → Sub Δ (Γ #)

  Sub- : Ctx → Ctx → Set
  Sub- Δ Γ = Sub Γ Δ

  variable
    s s' s'' : Sub Δ Γ
    σ σ' σ'' : Sub Δ Γ
    τ τ' τ'' : Sub Δ Γ

  -- composition operation for weakening after substitution
  trimSub : Δ ⊆ Γ → Sub Γ' Γ → Sub Γ' Δ
  trimSub base      []         = []
  trimSub (drop w)  (s `, x)   = trimSub w s
  trimSub (keep w)  (s `, x)   = (trimSub w s) `, x
  trimSub (keep# w) (lock s x) = lock (trimSub w s) x

  -- apply substitution to a variable
  substVar : Sub Γ Δ → Var Δ a → Tm Γ a
  substVar (s `, t)  zero     = t
  substVar (s `, _t) (succ v) = substVar s v

  -- weaken a substitution
  wkSub : Γ ⊆ Γ' → Sub Γ Δ → Sub Γ' Δ
  wkSub w []         = []
  wkSub w (s `, t)   = wkSub w s `, wkTm w t
  wkSub w (lock s e) = lock (wkSub (factorWk e w) s) (factorExt e w)

  -- NOTE: composition requires parallel substitution for terms

  -- "drop" the last variable in the context
  dropₛ : Sub Γ Δ → Sub (Γ `, a) Δ
  dropₛ s = wkSub fresh s

  -- "keep" the last variable in the context
  keepₛ : Sub Γ Δ → Sub (Γ `, a) (Δ `, a)
  keepₛ s = dropₛ s `, var zero

  -- "keep" the lock in the context
  keep#ₛ : Sub Γ Δ → Sub (Γ #) (Δ #)
  keep#ₛ s = lock s new

  -- embed a weakening to substitution
  embWk : Δ ⊆ Γ → Sub Γ Δ
  embWk base      = []
  embWk (drop  w) = dropₛ  (embWk w)
  embWk (keep  w) = keepₛ  (embWk w)
  embWk (keep# w) = keep#ₛ (embWk w)

  -- identity substitution
  idₛ : Sub Γ Γ
  idₛ = embWk idWk

  idₛ[_] = λ Γ → idₛ {Γ}

  ExtToSub : Acc Γ ΓL ΓR → Sub Γ (ΓL #)
  ExtToSub e = lock idₛ e

  module Composition
    (substTm     : {Δ Γ : Ctx} → {a : Ty} → (σ : Sub Δ Γ) → (t : Tm Γ a) → Tm Δ a)
    (lCtxₛ       : {Δ Γ ΓR Θ : Ctx} → (e : Acc Δ Γ ΓR) → (σ : Sub Θ Δ) → Ctx)
    (factorSubₛ  : ∀ {Δ Γ ΓR Θ : Ctx} (e : Acc Δ Γ ΓR) (σ : Sub Θ Δ) → Sub (lCtxₛ e σ) Γ)
    (rCtxₛ       : {Δ Γ ΓR Θ : Ctx} → (e : Acc Δ Γ ΓR) → (σ : Sub Θ Δ) → Ctx)
    (factorExtₛ  : ∀ {Δ Γ ΓR Θ : Ctx} (e : Acc Δ Γ ΓR) (σ : Sub Θ Δ) → Acc Θ (lCtxₛ e σ) (rCtxₛ e σ))
    where

    infixr 20 _∙ₛ_

    -- substitution composition
    _∙ₛ_ : Sub Δ Γ → Sub Δ' Δ → Sub Δ' Γ
    []        ∙ₛ s = []
    (s' `, t) ∙ₛ s = s' ∙ₛ s `, substTm s t
    lock s' e ∙ₛ s = lock (s' ∙ₛ factorSubₛ e s) (factorExtₛ e s)
