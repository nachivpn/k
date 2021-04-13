module IK.Completeness.Completeness where

open import IK.Term
open import IK.Norm
open import IK.Conversion
open import IK.Completeness.Trace

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; cong ; cong₂ ; trans)

complete : {t t' : Tm Γ a}
  → ({Δ : Ctx} {γ : Sub' Δ Γ} → eval t γ ≡ eval t' γ)
  → t ≈ t'
complete {t = t} {t'} f with f {_} {idₛ'}
... | p = trans-≈
  (trans-≈
    (⟶*-to-≈ (trace t))
    (≡-to-≈ (cong embNf (cong reify p))))
  (sym-≈ (⟶*-to-≈ (trace t')))
