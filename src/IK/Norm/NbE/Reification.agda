{-# OPTIONS --without-K #-}
module IK.Norm.NbE.Reification where

open import Data.Unit    using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open import FunExt

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

------------------------------------------------
-- reflect and reify are natural transformations
------------------------------------------------

-- reflect : Ne- a →̇ Tm'- a
-- reify   : Tm'- a →̇ Nf'- a

-- naturality of reflect
nat-reflect : (w : Γ ⊆ Γ') (n : Ne Γ a) → reflect (wkNe w n) ≡ wkTm' w (reflect n)
nat-reflect {a = 𝕓}     w n = refl
nat-reflect {a = a ⇒ b} w n = funexti' (λ _ → funext (λ _ → funext (λ _
  → cong (λ z → reflect (app z (reify _))) (wkNePres∙ w _ n))))
nat-reflect {a = □ a}  w n = cong box (nat-reflect (keep🔒 w) (unbox n nil))

-- image of reflect is in Psh
psh-reflect : (n : Ne Γ a) → Psh (reflect n)
-- naturality of reify
nat-reify : (w : Γ ⊆ Γ') (x : Tm' Γ a) → Psh x → reify (wkTm' w x) ≡ wkNf w (reify x)

-- psh-reflect
psh-reflect {a = 𝕓}     n = tt
psh-reflect {a = a ⇒ b} n = λ w x px
  → (λ w' → trans
       (cong reflect
         (cong₂ app (sym (wkNePres∙ _ _ _)) (nat-reify _ _ px)))
       (nat-reflect w' (app (wkNe w n) (reify x))))
  , psh-reflect (app (wkNe w n) _)
psh-reflect {a = □ a}  n = psh-reflect (unbox n nil)

-- nat-reify
nat-reify {a = 𝕓}         w x   px
  = refl
nat-reify {Γ} {a = a ⇒ b} w f   pf
  = let (nf , pfx) = pf fresh (reflect (var ze)) (psh-reflect {Γ = _ `, a} (var ze))
  in cong lam
    (trans
      (cong reify
        (trans
          (cong₂ f
            (cong drop (trans (rightIdWk _) (sym (leftIdWk _))))
            (nat-reflect (keep w) (var ze)))
          (nf (keep w))))
      (nat-reify (keep w) (f fresh (reflect (var ze))) pfx))
nat-reify {a = □ a} w  (box x) px
  = cong box (nat-reify (keep🔒 w) x px)

-- idₛ' is in Pshₛ
psh-idₛ' : Pshₛ (idₛ' {Γ})
psh-idₛ' {[]}     = tt
psh-idₛ' {Γ `, a} = wkSub'PresPsh fresh (idₛ' {Γ}) (psh-idₛ' {Γ}) , psh-reflect {Γ `, a} (var ze)
psh-idₛ' {Γ 🔒}    = psh-idₛ' {Γ}
