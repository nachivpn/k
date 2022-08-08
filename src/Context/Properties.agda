{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Context.Properties (Ty : Set) (Ty-Decidable : Decidable (_≡_ {A = Ty})) where

open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.Unit
  using (⊤ ; tt)

open import Relation.Nullary
  using (_because_ ; yes ; no)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; subst ; subst₂ ; cong ; cong₂)

open import Context.Base Ty

open import PEUtil

private
  variable
    a b c d : Ty

-----------
-- Contexts
-----------

Ctx-Decidable : Decidable (_≡_ {A = Ctx})
Ctx-Decidable []       []       = yes refl
Ctx-Decidable []       (Γ `, a) = no  λ ()
Ctx-Decidable []       (Γ #)    = no  λ ()
Ctx-Decidable (Γ `, a) []       = no  λ ()
Ctx-Decidable (Γ `, a) (Δ `, b) with Ctx-Decidable Γ Δ | Ty-Decidable a b
... | yes Γ≡Δ  | yes a≡b        = yes (cong₂ _`,_ Γ≡Δ a≡b)
... | yes Γ≡Δ  | no  ¬a≡b       = no  λ { refl → ¬a≡b refl }
... | no  ¬Γ≡Δ | yes a≡b        = no  λ { refl → ¬Γ≡Δ refl }
... | no  ¬Γ≡Δ | no  ¬a≡b       = no  λ { refl → ¬a≡b refl }
Ctx-Decidable (Γ `, a) (Δ #)    = no  λ ()
Ctx-Decidable (Γ #)   []        = no  λ ()
Ctx-Decidable (Γ #)   (Δ `, a)  = no  λ ()
Ctx-Decidable (Γ #)   (Δ #)     with Ctx-Decidable Γ Δ
... | yes Γ≡Δ                   = yes (cong _# Γ≡Δ)
... | no  ¬Γ≡Δ                  = no  λ { refl → ¬Γ≡Δ refl }

open Decidable⇒K Ctx-Decidable public
  using    ()
  renaming (Decidable⇒K to Ctx-K ; Decidable⇒UIP to Ctx-irrelevant)

`,-injective-left : Γ `, a ≡ Δ `, b → Γ ≡ Δ
`,-injective-left refl = refl

`,-injective-right : Γ `, a ≡ Δ `, b → a ≡ b
`,-injective-right refl = refl

#-injective : Γ # ≡ Δ # → Γ ≡ Δ
#-injective refl = refl

private
  open import Data.Nat
  open import Data.Nat.Properties

  m≢n+1+m : ∀ m {n} → m ≢ n + suc m
  m≢n+1+m m m≡n+1+m = m≢1+m+n m (trans m≡n+1+m (+-comm _ (suc m)))

  length : (Γ : Ctx) → ℕ
  length []       = 0
  length (Γ `, a) = 1 + length Γ
  length (Γ #)    = 1 + length Γ

  lengthPres+ : ∀ Γ Δ → length (Γ ,, Δ) ≡ length Δ + length Γ
  lengthPres+ Γ []       = refl
  lengthPres+ Γ (Δ `, a) = cong suc (lengthPres+ Γ Δ)
  lengthPres+ Γ (Δ #)    = cong suc (lengthPres+ Γ Δ)

  module _ {A : Set} where
    Γ≡Γ,a-impossible₁ : Γ ≡ Γ `, a ,, Γ' → A
    Γ≡Γ,a-impossible₁ {Γ} {a} {Γ'} p = ⊥-elim (m≢n+1+m (length Γ) (trans (cong length p) (lengthPres+ (Γ `, a) Γ')))

    Γ≡Γ,a-impossible₂ : Γ ≡ Γ ,, Γ' `, a → A
    Γ≡Γ,a-impossible₂ {Γ} {Γ'} {a} p = ⊥-elim (m≢1+n+m (length Γ) (trans (cong length p) (cong suc (lengthPres+ Γ Γ'))))

    Γ≡Γ#-impossible₁ : Γ ≡ Γ # ,, Γ' → A
    Γ≡Γ#-impossible₁ {Γ} {Γ'} p = ⊥-elim (m≢n+1+m (length Γ) (trans (cong length p) (lengthPres+ (Γ #) Γ')))

    Γ≡Γ#-impossible₂ : Γ ≡ (Γ ,, Γ') # → A
    Γ≡Γ#-impossible₂ {Γ} {Γ'} p = ⊥-elim (m≢1+n+m (length Γ) (trans (cong length p) (cong suc (lengthPres+ Γ Γ'))))

,,-injective-right : Δ ,, Γ ≡ Δ ,, Γ' → Γ ≡ Γ'
,,-injective-right {Δ} {[]}     {[]}      p = refl
,,-injective-right {Δ} {[]}     {Γ' `, a} p = Γ≡Γ,a-impossible₂ p
,,-injective-right {Δ} {[]}     {Γ' #}    p = Γ≡Γ#-impossible₂ p
,,-injective-right {Δ} {Γ `, a} {[]}      p = Γ≡Γ,a-impossible₂ (sym p)
,,-injective-right {Δ} {Γ `, a} {Γ' `, b} p = cong₂ _`,_ (,,-injective-right (`,-injective-left p)) (`,-injective-right p)
,,-injective-right {Δ} {Γ #}   {[]}       p = Γ≡Γ#-impossible₂ (sym p)
,,-injective-right {Δ} {Γ #}   {Γ' #}     p = cong _# (,,-injective-right (#-injective p))

,,-assoc : (ΓLL ,, ΓLR) ,, ΓR ≡ ΓLL ,, (ΓLR ,, ΓR)
,,-assoc {ΓLL} {ΓLR} {[]}      = refl
,,-assoc {ΓLL} {ΓLR} {ΓR `, a} = cong (_`, a) (,,-assoc {ΓLL} {ΓLR})
,,-assoc {ΓLL} {ΓLR} {ΓR #}    = cong _#      (,,-assoc {ΓLL} {ΓLR})

,,-leftUnit : {Γ : Ctx} → [] ,, Γ ≡ Γ
,,-leftUnit {[]}     = refl
,,-leftUnit {Γ `, a} = cong (_`, _) ,,-leftUnit
,,-leftUnit {Γ #}    = cong _# ,,-leftUnit

-------------
-- Weakenings
-------------

-- weakening composition obeys the left identity law
leftIdWk : (w : Γ' ⊆ Γ) → idWk ∙ w ≡ w
leftIdWk base      = refl
leftIdWk (drop w)  = cong drop (leftIdWk w)
leftIdWk (keep w)  = cong keep (leftIdWk w)
leftIdWk (keep# w) = cong keep# (leftIdWk w)

-- weakening composition obeys the right identity law
rightIdWk : (w : Γ' ⊆ Γ) → w ∙ idWk ≡ w
rightIdWk base      = refl
rightIdWk (drop w)  = cong drop (rightIdWk w)
rightIdWk (keep w)  = cong keep (rightIdWk w)
rightIdWk (keep# w) = cong keep# (rightIdWk w)

-- weakening composition is associative
assocWk : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ4 ⊆ Γ3) (w2 : Γ3 ⊆ Γ2) → (w1 : Γ2 ⊆ Γ1)
  → (w3 ∙ w2) ∙ w1 ≡ w3 ∙ (w2 ∙ w1)
assocWk w3         w2         base       = refl
assocWk w3         w2         (drop w1)  = cong drop (assocWk w3 w2 w1)
assocWk w3         (drop w2)  (keep w1)  = cong drop (assocWk w3 w2 w1)
assocWk (drop w3)  (keep w2)  (keep w1)  = cong drop (assocWk w3 w2 w1)
assocWk (keep w3)  (keep w2)  (keep w1)  = cong keep (assocWk w3 w2 w1)
assocWk (keep# w3) (keep# w2) (keep# w1) = cong keep# (assocWk w3 w2 w1)

fresh-keep : fresh[ a ] ∙ keep[ a ] w ≡ w ∙ fresh[ a ]
fresh-keep = cong drop (trans˘ (leftIdWk _) (rightIdWk _))

------------
-- Variables
------------

wkVarPresId : (x : Var Γ a) → wkVar idWk x ≡ x
wkVarPresId zero     = refl
wkVarPresId (succ x) = cong succ (wkVarPresId x)

-- weakening a variable index increments
wkIncr : (x : Var Γ a) → wkVar fresh[ b ] x ≡ succ x
wkIncr zero     = refl
wkIncr (succ x) = cong succ (cong succ (wkVarPresId x))

-- weakening of variables (a functor map) preserves weakening composition
wkVarPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (x : Var Γ a)
  → wkVar w' (wkVar w x) ≡ wkVar (w ∙ w') x
wkVarPres∙ (drop w) (drop w') zero     = cong succ (wkVarPres∙ (drop w) w' zero)
wkVarPres∙ (drop w) (keep w') zero     = cong succ (wkVarPres∙ w w' zero)
wkVarPres∙ (keep w) (drop w') zero     = cong succ (wkVarPres∙ (keep w) w' zero)
wkVarPres∙ (keep w) (keep w') zero     = refl
wkVarPres∙ (drop w) (drop w') (succ x) = cong succ (wkVarPres∙ (drop w) w' (succ x))
wkVarPres∙ (drop w) (keep w') (succ x) = cong succ (wkVarPres∙ w w' (succ x))
wkVarPres∙ (keep w) (drop w') (succ x) = cong succ (wkVarPres∙ (keep w) w' (succ x))
wkVarPres∙ (keep w) (keep w') (succ x) = cong succ (wkVarPres∙ w w' x)

--------------------
-- Context extension
--------------------

-- Proof of WL is irrelevant
WLIsProp : (x x' : WL θ) → x ≡ x'
WLIsProp {tt} tt tt = refl

-- Proof of Ext is irrelevant
private
  ExtIsProp' : (e : Ext θ Γ ΓL ΓR) → (e' : Ext θ Γ ΓL' ΓR') → (pl : ΓL' ≡ ΓL) → (pr : ΓR' ≡ ΓR) → e ≡ subst₂ (Ext θ Γ) pl pr e'
  ExtIsProp' nil           nil          pl   pr with Ctx-K pl
  ... | refl with Ctx-K pr
  ... | refl = refl
  ExtIsProp' nil           (ext _e)     _pl  ()
  ExtIsProp' nil           (ext# _x _e) _pl  ()
  ExtIsProp' (ext e)       nil          _pl  ()
  ExtIsProp' (ext e)       (ext e')     refl pr with `,-injective-left pr
  ... | refl with Ctx-K pr
  ... | refl = cong ext (ExtIsProp' e e' refl refl)
  ExtIsProp' (ext# _x _e) nil           _pl  ()
  ExtIsProp' (ext#  x  e) (ext# x' e')  refl pr with #-injective pr
  ... | refl with Ctx-K pr
  ... | refl = cong₂ ext# (WLIsProp x x') (ExtIsProp' e e' refl refl)

ExtIsProp : (e e' : Ext θ Γ ΓL ΓR) → e ≡ e'
ExtIsProp e e' = ExtIsProp' e e' refl refl

-- LFExt is indeed a lock-free extension
LFExtIs#-free : LFExt Γ ΓL ΓR → #-free ΓR
LFExtIs#-free nil     = tt
LFExtIs#-free (ext e) = LFExtIs#-free e

-- extension is appending
extIs,, : Ext θ Γ ΓL ΓR → Γ ≡ (ΓL ,, ΓR)
extIs,, nil        = refl
extIs,, (ext e)    = cong (_`, _) (extIs,, e)
extIs,, (ext# f e) = cong _# (extIs,, e)

-- appending (potentially) with locks is an extension
,,IsExt : CExt (ΓL ,, ΓR) ΓL ΓR
,,IsExt {ΓL = ΓL} {[]}      = nil
,,IsExt {ΓL = ΓL} {ΓR `, x} = ext ,,IsExt
,,IsExt {ΓL = ΓL} {ΓR #}    = ext# tt ,,IsExt

-- appending without locks is an extension
,,IsExtLF : #-free ΓR → LFExt (ΓL ,, ΓR) ΓL ΓR
,,IsExtLF {[]}      p = nil
,,IsExtLF {ΓR `, x} p = ext (,,IsExtLF p)

-- NOTE: `extIs,,` + `,,IsExt` implies that `Ext` is the call-graph of `_,,_`

-- extensions are unique
-- i.e., an extension of ΓL with ΓR must yield a unique extension
extLUniq : Ext θ Γ' ΓL ΓR → Ext θ Γ ΓL ΓR → Γ' ≡ Γ
extLUniq nil        nil         = refl
extLUniq (ext e)    (ext e')    = cong (_`, _) (extLUniq e e')
extLUniq (ext# f e) (ext# _ e') = cong _# (extLUniq e e')

private
  module _ {A : Set} where
    Γ,aRΓ-impossible : Ext θ Γ (Γ `, a) ΓR → A
    Γ,aRΓ-impossible e = Γ≡Γ,a-impossible₁ (extIs,, e)

    Γ#RΓ-impossible : Ext θ Γ (Γ #) ΓR → A
    Γ#RΓ-impossible e = Γ≡Γ#-impossible₁ (extIs,, e)

extRUniq : Ext θ Γ ΓL ΓR → Ext θ Γ ΓL ΓR' → ΓR ≡ ΓR'
extRUniq e e' = ,,-injective-right (˘trans (extIs,, e) (extIs,, e'))

extRUniq′ : ΓL ≡ ΓL' → Ext θ Γ ΓL ΓR → Ext θ Γ ΓL' ΓR' → ΓR ≡ ΓR'
extRUniq′ refl = extRUniq

ExtIsProp′ : (e : Ext θ Γ ΓL ΓR) → (e' : Ext θ Γ ΓL ΓR') → subst (Ext θ Γ ΓL) (extRUniq e e') e ≡ e'
ExtIsProp′ _ _ = ExtIsProp _ _

-- extension is assocative
extLAssoc : Ext θ Γ ΓL ΓR  → Ext θ ΓR ΓRL ΓRR → Ext θ Γ (ΓL ,, ΓRL) ΓRR
extLAssoc el          nil         rewrite extIs,, el = nil
extLAssoc (ext    el) (ext    er)                    = ext    (extLAssoc el er)
extLAssoc (ext# x el) (ext# _ er)                    = ext# x (extLAssoc el er)

extLeftUnit : extRAssoc nil e ≡ subst˘ (CExt _ _) ,,-leftUnit e
extLeftUnit = ExtIsProp _ _

-------------------------------------
-- Operations on lock-free extensions
-------------------------------------

-- left unweaken the (lock-free) extension of a context
leftUnwkLFExt : (e : LFExt (Δ ,, Γ) (Δ ,, ΓL) ΓR) → LFExt Γ ΓL ΓR
leftUnwkLFExt {Δ} {Γ} {ΓL} {ΓR} e = subst (λ Γ → LFExt Γ ΓL ΓR) obs (,,IsExtLF (LFExtIs#-free e))
  where
    obs : ΓL ,, ΓR ≡ Γ
    obs = ,,-injective-right (sym (extIs,, (extRAssoc ,,IsExt (upLFExt e))))

-- the operation ←# returns the context to the left of # so applying
-- it to a lock-free extension does not change the result; special
-- case: if LFExt Γ (ΓL #) ΓR then ←# Γ ≡ ΓL
←#IsPre# : (e : LFExt Γ ΓL ΓR) → ←# ΓL ≡ ←# Γ
←#IsPre# nil     = refl
←#IsPre# (ext e) = ←#IsPre# e

-- the operation #→ returns the context to the right of #
private
  #→IsPost#' : (e : LFExt Γ ΓL ΓR) → #→ ΓL ,, ΓR ≡ #→ Γ
  #→IsPost#' nil     = refl
  #→IsPost#' (ext e) = cong (_`, _) (#→IsPost#' e)

#→IsPost# : (e : LFExt Γ (ΓL #) ΓR) → ΓR ≡ #→ Γ
#→IsPost# {Γ} e = subst (_≡ #→ Γ) ,,-leftUnit (#→IsPost#' e)

LFExtToWkPresTrans : (e : LFExt ΓL ΓLL ΓLR) (e' : LFExt Γ ΓL ΓR)
  → LFExtToWk (extRAssoc e e') ≡ LFExtToWk e ∙ LFExtToWk e'
LFExtToWkPresTrans e nil      = sym (rightIdWk (LFExtToWk e))
LFExtToWkPresTrans e (ext e') = cong drop (LFExtToWkPresTrans e e')

----------------------------------------
-- Slicing laws for lock-free extensions
----------------------------------------

wkLFExtPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (e : LFExt Γ (ΓL #) ΓR)
  → wkLFExt (wkLFExt e w) w' ≡ wkLFExt e (w ∙ w')
wkLFExtPres∙ _ _ _ = ExtIsProp _ _

sliceLeftPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (e : LFExt Γ (ΓL #) ΓR)
  → (sliceLeft e w ∙ sliceLeft (wkLFExt e w) w') ≡ sliceLeft e (w ∙ w')
sliceLeftPres∙ (drop  w) (drop  w') nil     = sliceLeftPres∙ (drop  w) w' nil
sliceLeftPres∙ (drop  w) (drop  w') (ext e) = sliceLeftPres∙ (drop  w) w' (ext e)
sliceLeftPres∙ (drop  w) (keep  w') nil     = sliceLeftPres∙ w         w' nil
sliceLeftPres∙ (drop  w) (keep  w') (ext e) = sliceLeftPres∙ w         w' (ext e)
sliceLeftPres∙ (keep  w) (drop  w') (ext e) = sliceLeftPres∙ (keep  w) w' (ext e)
sliceLeftPres∙ (keep  w) (keep  w') (ext e) = sliceLeftPres∙ w         w' e
sliceLeftPres∙ (keep# w) (drop  w') nil     = sliceLeftPres∙ (keep# w) w' nil
sliceLeftPres∙ (keep# w) (keep# w') nil     = refl

-- roughly, slicing a weakening into two weakenings, one to left of the lock,
-- and the other to right, must not change its composition.
slicingLemma : (w : Γ ⊆ Γ') → (e : LFExt Γ (ΓL #) ΓR)
  → LFExtToWk e ∙ w ≡ (keep# (sliceLeft e w) ∙ sliceRight e w)
slicingLemma (drop  w) nil     = cong drop  (slicingLemma w nil)
slicingLemma (drop  w) (ext e) = cong drop  (slicingLemma w (ext e))
slicingLemma (keep  w) (ext e) = cong drop  (slicingLemma w e)
slicingLemma (keep# w) nil     = cong keep# (trans˘ (leftIdWk w) (rightIdWk w))

private
  sliceLeftId' : (e : LFExt Γ (ΓL #) ΓR)
    → sliceLeft e idWk[ Γ ] ≡ subst (ΓL ⊆_) (←#IsPre# e) idWk[ ΓL ]
  sliceLeftId' {Γ = _Γ #}     nil     = refl
  sliceLeftId' {Γ = _Γ `, _a} (ext e) = sliceLeftId' e

  sliceLeftDrop' : (e : LFExt Γ (ΓL #) ΓR) → (w : LFExt Γ' Γ ΓR')
    → sliceLeft e (LFExtToWk w) ≡ subst (ΓL ⊆_) (←#IsPre# (e ∙Ext w)) idWk[ ΓL ]
  sliceLeftDrop' e         nil     = sliceLeftId'   e
  sliceLeftDrop' e@nil     (ext w) = sliceLeftDrop' e w
  sliceLeftDrop' e@(ext _) (ext w) = sliceLeftDrop' e w

sliceLeftDrop : (e : LFExt Γ (←# Γ #) ΓR) → (w : LFExt Γ' Γ ΓR')
  → sliceLeft e (LFExtToWk w) ≡ subst (←# Γ ⊆_) (←#IsPre# w) idWk[ ←# Γ ]
sliceLeftDrop e w rewrite Ctx-irrelevant (←#IsPre# w) (←#IsPre# (e ∙Ext w)) = sliceLeftDrop' e w

sliceLeftId : (e : LFExt Γ (←# Γ #) ΓR) → sliceLeft e idWk[ Γ ] ≡ idWk[ ←# Γ ]
sliceLeftId e = sliceLeftDrop e nil

wkLFExtDrop : (e : LFExt Γ (←# Γ #) (#→ Γ)) → (w : LFExt Γ' Γ ΓR)
  → wkLFExt e (LFExtToWk w) ≡ subst₂ (λ ΓL ΓR → LFExt Γ' (ΓL #) ΓR) (←#IsPre# w) (#→IsPost#' w) (e ∙Ext w)
wkLFExtDrop _e _w = ExtIsProp _ _

wkLFExtPresId : (e : LFExt Γ (←# Γ #) (#→ Γ)) → wkLFExt e idWk ≡ e
wkLFExtPresId e = wkLFExtDrop e nil

sliceRightId : (e : LFExt Γ (←# Γ #) (#→ Γ)) → sliceRight e idWk ≡ LFExtToWk e
sliceRightId e rewrite wkLFExtPresId e = refl

--------------------------------------------
-- Factorisation laws for general extensions
--------------------------------------------

lCtxPresId : (e : CExt Γ ΓL ΓR) → lCtx e idWk ≡ ΓL
lCtxPresId nil       = refl
lCtxPresId (ext e)   = lCtxPresId e
lCtxPresId (ext#- e) = lCtxPresId e

rCtxPresId : (e : CExt Γ ΓL ΓR) → rCtx e idWk ≡ ΓR
rCtxPresId nil       = refl
rCtxPresId (ext e)   = cong (_`, _) (rCtxPresId e)
rCtxPresId (ext#- e) = cong _# (rCtxPresId e)

factorWkPresId : (e : CExt Γ ΓL ΓR) → subst (ΓL ⊆_) (lCtxPresId e) (factorWk e idWk) ≡ idWk[ ΓL ]
factorWkPresId nil       = refl
factorWkPresId (ext e)   = factorWkPresId e
factorWkPresId (ext#- e) = factorWkPresId e

factorExtPresId : (e : CExt Γ ΓL ΓR) → subst₂ (CExt Γ) (lCtxPresId e) (rCtxPresId e) (factorExt e idWk) ≡ e
factorExtPresId _ = ExtIsProp _ _

lCtxPres∙ : (e : Ext θ Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → lCtx e (w ∙ w') ≡ lCtx (factorExt e w) w'
lCtxPres∙ nil          w           w'         = refl
lCtxPres∙ e@(ext _)    w@(drop _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext _)    w@(keep _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext# f _) w@(drop _)  (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext# f _) w@(keep# _) (drop w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext _)    (drop w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ e@(ext# f _) (drop w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ (ext e)      (keep w)    (keep w')  = lCtxPres∙ e w w'
lCtxPres∙ (ext# f e)   (keep# w)   (keep# w') = lCtxPres∙ e w w'

rCtxPres∙ : (e : Ext θ Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → rCtx e (w ∙ w') ≡ rCtx (factorExt e w) w'
rCtxPres∙ nil          w           w'         = refl
rCtxPres∙ e@(ext _)    w@(drop _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext _)    w@(keep _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext# f _) w@(drop _)  (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext# f _) w@(keep# _) (drop w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext _)    (drop w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ e@(ext# f _) (drop w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ (ext e)      (keep w)    (keep w')  = cong (_`, _) (rCtxPres∙ e w w')
rCtxPres∙ (ext# f e)   (keep# w)   (keep# w') = cong _# (rCtxPres∙ e w w')

factorWkPres∙ : ∀ (e : Ext θ Γ ΓL ΓR) (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') → subst (ΓL ⊆_) (lCtxPres∙ e w w') (factorWk e (w ∙ w')) ≡ factorWk e w ∙ factorWk (factorExt e w) w'
factorWkPres∙ nil          w           w'         = refl
factorWkPres∙ e@(ext _)    w@(drop _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext _)    w@(keep _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext# f _) w@(drop _)  (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext# f _) w@(keep# _) (drop w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext _)    (drop w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ e@(ext# f _) (drop w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ (ext e)      (keep w)    (keep w')  = factorWkPres∙ e w w'
factorWkPres∙ (ext# f e)   (keep# w)   (keep# w') = factorWkPres∙ e w w'

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
lCtxPresTrans e  e'@(ext# f _) (drop w)  = lCtxPresTrans e e' w
lCtxPresTrans e  (ext# f e')   (keep# w) = lCtxPresTrans e e' w

rCtxPresTrans : ∀ (e : Ext θ Δ Γ ΓR) (e' : Ext θ Θ Δ ΔR) (w : Θ ⊆ Θ') → rCtx (extRAssoc e e') w ≡ rCtx e (factorWk e' w) ,, rCtx e' w
rCtxPresTrans _e nil          _w               = refl
rCtxPresTrans e e'@(ext _)    (drop {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e (ext e')      (keep {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e e'@(ext# f _) (drop {a = a} w) = cong (_`, a) (rCtxPresTrans e e' w)
rCtxPresTrans e (ext# f e')   (keep# w)        = cong (_#) (rCtxPresTrans e e' w)

factorWkPresTrans : ∀ (e : Ext θ Δ Γ ΓR) (e' : Ext θ Θ Δ ΔR) (w : Θ ⊆ Θ') → subst (Γ ⊆_) (lCtxPresTrans e e' w) (factorWk (extRAssoc e e') w) ≡ factorWk e (factorWk e' w)
factorWkPresTrans _e nil           _w        = refl
factorWkPresTrans e  e'@(ext _)    (drop w)  = factorWkPresTrans e e' w
factorWkPresTrans e  (ext e')      (keep w)  = factorWkPresTrans e e' w
factorWkPresTrans e  e'@(ext# f _) (drop w)  = factorWkPresTrans e e' w
factorWkPresTrans e  (ext# f e')   (keep# w) = factorWkPresTrans e e' w

factorExtPresTrans : ∀ (e : CExt Δ Γ ΓR) (e' : CExt Θ Δ ΔR) (w : Θ ⊆ Θ') → subst₂ (CExt Θ') (lCtxPresTrans e e' w) (rCtxPresTrans e e' w) (factorExt (extRAssoc e e') w) ≡ extRAssoc (factorExt e (factorWk e' w)) (factorExt e' w)
factorExtPresTrans _e _e' _w = ExtIsProp _ _


-- Special case of factorWk

rCtx′ : (e : CExt Γ ΓL ΓR) → (e' : LFExt Γ' Γ ΓR') → Ctx
rCtx′ {ΓR' = .[]} _e        nil       = []
rCtx′ {ΓR' = ΓR'} nil       (ext _e') = ΓR'
rCtx′ {ΓR' = ΓR'} (ext   e) (ext  e') = rCtx′ (ext   e) e'
rCtx′ {ΓR' = ΓR'} (ext#- e) (ext  e') = rCtx′ (ext#- e) e'

-- Special case of factorWk where the second argument consists of only drops (simulated using LFExt)
factorDropsWk : (e : CExt Γ ΓL ΓR) → (e' : LFExt Γ' Γ ΓR') → LFExt (lCtx e (LFExtToWk e')) ΓL (rCtx′ e e')
factorDropsWk {ΓR' = .[]} e         nil      = subst (λ ΓL → LFExt (lCtx e idWk) ΓL _) (lCtxPresId e) nil
factorDropsWk {ΓR' = ΓR'} nil       (ext e') = ext e'
factorDropsWk {ΓR' = ΓR'} (ext   e) (ext e') = factorDropsWk (ext   e) e'
factorDropsWk {ΓR' = ΓR'} (ext#- e) (ext e') = factorDropsWk (ext#- e) e'

-- factorDropsWk is indeed a special case of factorWk
factorDropsWkIsfactorWk : (e : CExt Γ ΓL ΓR) → (e' : LFExt Γ' Γ ΓR') → LFExtToWk (factorDropsWk e e') ≡ factorWk e (LFExtToWk e')
factorDropsWkIsfactorWk nil       nil       = refl
factorDropsWkIsfactorWk nil       (ext _e') = refl
factorDropsWkIsfactorWk (ext   e) nil       = factorDropsWkIsfactorWk e         nil
factorDropsWkIsfactorWk (ext   e) (ext  e') = factorDropsWkIsfactorWk (ext   e) e'
factorDropsWkIsfactorWk (ext#- e) nil       = factorDropsWkIsfactorWk e         nil
factorDropsWkIsfactorWk (ext#- e) (ext  e') = factorDropsWkIsfactorWk (ext#- e) e'

-- Note: factorDropsExt is not need as it has the same type as factorDrops and ExtIsProp

factorisationLemma : (e : LFExt Γ ΓL ΓR) → (w : Γ ⊆ Γ')
  → LFExtToWk e ∙ w ≡ factorWk e w ∙ LFExtToWk (factorExt e w)
factorisationLemma nil     w        = trans˘ (leftIdWk w) (rightIdWk w)
factorisationLemma (ext e) (drop w) = cong drop (factorisationLemma (ext e) w)
factorisationLemma (ext e) (keep w) = cong drop (factorisationLemma e      w)

-- Properties about absorption of upLFExt

lCtxAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → lCtx {θ = ff} e w ≡ lCtx {θ = tt} (upLFExt e) w
lCtxAbsorbsUpLFExt nil     _w       = refl
lCtxAbsorbsUpLFExt (ext e) (drop w) = lCtxAbsorbsUpLFExt (ext e) w
lCtxAbsorbsUpLFExt (ext e) (keep w) = lCtxAbsorbsUpLFExt e       w

rCtxAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → rCtx {θ = ff} e w ≡ rCtx {θ = tt} (upLFExt e) w
rCtxAbsorbsUpLFExt nil     _w       = refl
rCtxAbsorbsUpLFExt (ext e) (drop w) = cong (_`, _) (rCtxAbsorbsUpLFExt (ext e) w)
rCtxAbsorbsUpLFExt (ext e) (keep w) = cong (_`, _) (rCtxAbsorbsUpLFExt e       w)

factorWkAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → subst (_ ⊆_) (lCtxAbsorbsUpLFExt e w) (factorWk e w) ≡ factorWk (upLFExt e) w
factorWkAbsorbsUpLFExt nil     _w       = refl
factorWkAbsorbsUpLFExt (ext e) (drop w) = factorWkAbsorbsUpLFExt (ext e) w
factorWkAbsorbsUpLFExt (ext e) (keep w) = factorWkAbsorbsUpLFExt e       w

factorExtAbsorbsUpLFExt : (e : LFExt Γ ΓL ΓR) (w : Γ ⊆ Γ') → subst₂ (CExt _) (lCtxAbsorbsUpLFExt e w) (rCtxAbsorbsUpLFExt e w) (upLFExt (factorExt e w)) ≡ factorExt (upLFExt e) w
factorExtAbsorbsUpLFExt _ _ = ExtIsProp _ _
