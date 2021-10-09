{-# OPTIONS --allow-unsolved-metas #-}
module IS4.Norm where

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)

open import Relation.Binary.PropositionalEquality  using (_≡_)

open import IS4.NbE

open import IS4.Term

-------------------------
-- Normalization function
-------------------------

-- retraction of interpretation
quot : evalCtx Γ →̇ evalTy a → Nf Γ a
quot {Γ} {a} α = reify a (α .apply (idₛ' Γ))

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (evalTm t)

norm-complete : t ≈ t' → norm t ≡ norm t'
norm-complete {Γ} {a} t≈t' = reify-pres-≋ a (apply-sq (evalTm-sound' t≈t') ≋-refl[ evalCtx Γ ])

norm-sound : norm t ≡ norm t' → t ≈ t'
norm-sound = {!!}
