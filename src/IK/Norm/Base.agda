{-# OPTIONS --without-K #-}
module IK.Norm.Base where

open import Data.Unit    using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_)

open import IK.Norm.NbE.Model
open import IK.Norm.NbE.Reification

open import IK.Term

-------------------------
-- Normalization function
-------------------------

-- retraction of interpretation
quot : (Sub'- Γ →̇ Tm'- a) → Nf Γ a
quot f = reify (f idₛ')

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (eval t)

----------------------------------
-- Normalization for substitutions
----------------------------------

-- (simply "do everything pointwise")

-- retraction of evalₛ
quotₛ : Sub'- Γ →̇ Nfₛ- Γ
quotₛ {[]}     tt         = []
quotₛ {Γ `, _} (s , x)    = (quotₛ s) `, (reify x)
quotₛ {Γ #}    (lock s e) = lock (quotₛ s) e

-- normalization function, for substitutions
normₛ : Sub Δ Γ → Nfₛ Δ Γ
normₛ s = quotₛ (evalₛ s idₛ')
