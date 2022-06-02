{-# OPTIONS --safe --with-K #-}
module IK.Completeness.Completeness where

open import IK.Term
open import IK.Norm
open import IK.Conversion
open import IK.Completeness.Trace

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; trans)

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
