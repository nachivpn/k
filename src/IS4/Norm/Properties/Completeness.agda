module IS4.Norm.Properties.Completeness where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import IS4.Norm.Base

open import IS4.Norm.NbE.Model
open import IS4.Norm.NbE.Reification

open import IS4.Term

norm-complete : (t≈u : t ≈ u) → norm t ≡ norm u
norm-complete {Γ} {a} t≈u = reify-pres-≋ a (apply-sq (evalTm-sound' t≈u) ≋[ evalCtx Γ ]-refl)
