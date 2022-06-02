{-# OPTIONS --safe --with-K #-}
module IS4.Norm.Base where

open import Data.Unit    using (tt)
open import Data.Product using (_,_)

open import IS4.Norm.NbE.Model
open import IS4.Norm.NbE.Reification

open import IS4.Term

-- retraction of interpretation
quot : Sub'- Γ →̇ Tm'- a → Nf Γ a
quot {Γ} {a} f = reify a (f (idₛ' Γ))

-- retraction of evalₛ (simply "do everything pointwise")
quotₛ : Sub'- Γ →̇ Nfₛ- Γ
quotₛ {[]}     tt                        = []
quotₛ {Γ `, a} (elem (s , x))            = quotₛ s `, reify a x
quotₛ {Γ 🔒}   (elem (ΓL , (ΓR , e) , s)) = lock (quotₛ s) e

-- normalization function
norm : Tm Γ a → Nf Γ a
norm t = quot (eval t)

-- normalization function, for substitutions
normₛ : Sub Δ Γ → Nfₛ Δ Γ
normₛ {Γ} s = quotₛ (evalₛ s (idₛ' Γ))
