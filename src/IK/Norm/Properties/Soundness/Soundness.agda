{-# OPTIONS --safe --without-K #-}
module IK.Norm.Properties.Soundness.Soundness where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; trans)

open import IK.Norm.Base

open import IK.Norm.NbE.Model
open import IK.Norm.NbE.Reification

open import IK.Norm.Properties.Soundness.Trace

open import IK.Term

--
-- This module proves the completeness of evaluation (eval-complete),
-- from which the soundness of normalization (norm-sound) follows.
--

eval-complete : {t t' : Tm Γ a}
  → ({Δ : Ctx} {γ : Sub' Δ Γ} → eval t γ ≡ eval t' γ)
  → t ≈ t'
eval-complete {t = t} {t'} f with f {_} {idₛ'}
... | p = ≈-trans
  (≈-trans
    (⟶*-to-≈ (trace t))
    (≡-to-≈ (cong embNf (cong reify p))))
  (≈-sym (⟶*-to-≈ (trace t')))

norm-sound : norm t ≡ norm u → t ≈ u
norm-sound {t = t} {u} t'≡u' = ≈-trans
  (⟶*-to-≈ (trace t))
  (≈-trans
    (≡-to-≈ (cong embNf t'≡u'))
    (≈-sym (⟶*-to-≈ (trace u))))
