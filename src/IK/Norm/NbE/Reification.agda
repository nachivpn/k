{-# OPTIONS --safe --with-K #-}
module IK.Norm.NbE.Reification where

open import Data.Unit    using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_)

open import IK.Norm.NbE.Model

open import IK.Term

reify   : Tm' Γ a → Nf Γ a
reflect : Ne Γ a  → Tm' Γ a

-- interpretation of neutrals
reflect {a = 𝕓} n     = up𝕓 n
reflect {a = a ⇒ b} n = λ e x → reflect (app (wkNe e n) (reify x))
reflect {a = □ a} n   = box (reflect (unbox n new))

-- reify values to normal forms
reify {a = 𝕓}     x       = x
reify {a = a ⇒ b} x       = lam (reify (x (drop idWk) (reflect (var ze))))
reify {a = □ a}   (box x) = box (reify x)

-- identity substitution
idₛ' : Sub' Γ Γ
idₛ' {[]}     = tt
idₛ' {Γ `, x} = wkSub' (drop idWk) idₛ' , reflect (var ze)
idₛ' {Γ 🔒}    = lock (idₛ' {Γ}) new
