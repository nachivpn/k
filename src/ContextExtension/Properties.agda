{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module ContextExtension.Properties (Ty : Set) (Ty-Decidable : Decidable (_≡_ {A = Ty})) where

open import Data.Product using (_,_)
open import Data.Unit    using (tt)

open import Relation.Binary.Definitions           using (Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; cong₂ ; subst ; subst₂)

open import PUtil
open import PEUtil

open import Context               Ty Ty-Decidable
open import Weakening             Ty
open import ContextExtension.Base Ty

private
  variable
    a b c d : Ty

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

-----------------------------------
-- Operations on general extensions
-----------------------------------

◁IS4-irrel : Irrelevant _◁IS4_
◁IS4-irrel (ΔR , Γ◁Δ) (ΔR' , Γ◁Δ') = Σ-≡,≡→≡ (extRUniq Γ◁Δ Γ◁Δ' , ExtIsProp _ _)

◁IS4-trans-assoc : ∀ (Γ◁Δ : Γ ◁IS4 Δ) (Δ◁Θ : Δ ◁IS4 Θ) (Θ◁Ξ : Θ ◁IS4 Ξ) → ◁IS4-trans Γ◁Δ (◁IS4-trans Δ◁Θ Θ◁Ξ) ≡ ◁IS4-trans (◁IS4-trans Γ◁Δ Δ◁Θ) Θ◁Ξ
◁IS4-trans-assoc _ _ _ = ◁IS4-irrel _ _

◁IS4-refl-unit-left : ∀ (Γ◁Δ : Γ ◁IS4 Δ) → ◁IS4-trans Γ◁Δ ◁IS4-refl ≡ Γ◁Δ
◁IS4-refl-unit-left _ = ◁IS4-irrel _ _

◁IS4-refl-unit-right : ∀ (Γ◁Δ : Γ ◁IS4 Δ) → ◁IS4-trans ◁IS4-refl Γ◁Δ ≡ Γ◁Δ
◁IS4-refl-unit-right _ = ◁IS4-irrel _ _

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
