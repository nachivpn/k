{-# OPTIONS --safe --without-K #-}
module IS4.Norm.NbE.Reification where

open import Data.Unit    using (⊤; tt)          renaming ()
open import Data.Product using (Σ; ∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂; module ≡-Reasoning)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import IS4.Norm.NbE.Model

open import IS4.Term hiding (factorWk)

reflect         : (a : Ty) → (n : Ne  Γ a) → Tm' Γ a
reflect-pres-≋  : ∀ (a : Ty) {n n' : Ne Γ a} (n≡n' : n ≡ n') → reflect a n ≋[ evalTy a ] reflect a n'
reflect-natural : ∀ (a : Ty) (n : Ne Γ a) (w : Γ ⊆ Γ') → reflect a (wkNe w n) ≋[ evalTy a ] wk[ evalTy a ] w (reflect a n)

reify         : (a : Ty) → (x : Tm' Γ a) → Nf  Γ a
reify-pres-≋  : ∀ (a : Ty) {x x' : Tm' Γ a} (x≋x' : x ≋[ evalTy a ] x') → reify a x ≡ reify a x'
reify-natural : ∀ (a : Ty) (x : Tm' Γ a) (w : Γ ⊆ Γ') → reify a (wk[ evalTy a ] w x) ≡ wkNf w (reify a x)

var0' : (a : Ty) → Tm' (Γ `, a) a
var0' a = reflect a (var zero)

-- interpretation of neutrals
reflect ι       n = n
reflect (a ⇒ b) n = record
  { fun     = λ w    p    → reflect b (app (wkNe w n) (reify a p))
  ; pres-≋  = λ w    p≋p' → reflect-pres-≋ b (cong (app (wkNe w n)) (reify-pres-≋ a p≋p'))
  ; natural = λ w w' p    → let open EqReasoning ≋[ evalTy b ]-setoid in begin
      wk[ evalTy b ] w' (reflect b (app (wkNe w n) (reify a p)))            ≈˘⟨ reflect-natural b _ w' ⟩
      reflect b (wkNe w' (app (wkNe w n) (reify a p)))                      ≡⟨⟩
      reflect b (app (wkNe w' (wkNe w n)) (wkNf w' (reify a p)))            ≡˘⟨ cong (λ m → reflect b (app _ m)) (reify-natural a p w') ⟩
      reflect b (app (wkNe w' (wkNe w n)) (reify a (wk[ evalTy a ] w' p)))  ≡⟨  cong (λ n → reflect b (app n _)) (wkNePres∙ w w' n) ⟩
      reflect b (app (wkNe (w ∙ w') n) (reify a (wk[ evalTy a ] w' p)))     ∎
  }
reflect (□ a) n = record
  { fun     = λ w (_ , e)    → reflect a (unbox (wkNe w n) e)
  ; natural = λ w r@(_ , e) w' → let open EqReasoning ≋[ evalTy a ]-setoid in begin
      reflect a (unbox (wkNe (w ∙ factorWk r w') n) (factorExt e w'))       ≡˘⟨ cong (λ n → reflect a (unbox n _)) (wkNePres∙ w (factorWk r w') n) ⟩
      reflect a (unbox (wkNe (factorWk r w') (wkNe w n)) (factorExt e w'))  ≡⟨⟩
      reflect a (wkNe w' (unbox (wkNe w n) e))                              ≈⟨  reflect-natural a (unbox (wkNe w n) e) w' ⟩
      wk[ evalTy a ] w' (reflect a (unbox (wkNe w n) e))                    ∎
  }

reflect-pres-≋ = λ a n≡n' → ≋[ evalTy a ]-reflexive (cong (reflect a) n≡n')

reflect-natural ι       n w = ≋[ evalTy ι ]-refl
reflect-natural (a ⇒ b) n w = record
  { pw = λ w' p → let open EqReasoning ≋[ evalTy b ]-setoid in begin
      reflect (a ⇒ b) (wkNe w n) .apply w' p                  ≡⟨⟩
      reflect b (app (wkNe w' (wkNe w n)) (reify a p))        ≡⟨ cong (λ n → reflect b (app n (reify a p))) (wkNePres∙ w w' n) ⟩
      reflect b (app (wkNe (w ∙ w') n) (reify a p))           ≡⟨⟩
      wk[ evalTy (a ⇒ b) ] w (reflect (a ⇒ b) n) .apply w' p  ∎
  }
reflect-natural (□ a) n w = record
  { pw = λ w' r@(_ , e) → let open EqReasoning ≋[ evalTy a ]-setoid in begin
      reflect (□ a) (wkNe w n) .apply w' r                ≡⟨⟩
      reflect a (unbox (wkNe w' (wkNe w n)) e)            ≡⟨ cong (λ n → reflect a (unbox n e)) (wkNePres∙ w w' n) ⟩
      reflect a (unbox (wkNe (w ∙ w') n) e)               ≡⟨⟩
      wk[ evalTy (□ a) ] w (reflect (□ a) n) .apply w' r  ∎
  }

-- reify values to normal forms
reify ι       n = up  n
reify (a ⇒ b) f = lam (reify b (f .apply fresh[ a ] (var0' a)))
reify (□ a)   b = box (reify a (b .apply idWk new◁IS4))

reify-pres-≋ ι       x≋x' = cong up  x≋x'
reify-pres-≋ (a ⇒ b) x≋x' = cong lam (reify-pres-≋ b (x≋x' .pw fresh[ a ] (var0' a)))
reify-pres-≋ (□ a)   x≋x' = cong box (reify-pres-≋ a (x≋x' .pw idWk new◁IS4))

reify-natural ι       x w = refl
reify-natural (a ⇒ b) x w = let open ≡-Reasoning in begin
  reify (a ⇒ b) (wk[ evalTy (a ⇒ b) ] w x)                                                      ≡⟨⟩
  lam (reify b (x .apply (w ∙ fresh[ a ])           (var0' a)))                                 ≡˘⟨ cong₂ (λ w n → lam (reify b (x .apply w (reflect a n)))) fresh-keep refl ⟩
  lam (reify b (x .apply (fresh[ a ] ∙ keep[ a ] w) (reflect a (wkNe (keep[ a ] w) var0))))     ≡⟨  cong lam (reify-pres-≋ b (x .apply-≋ _ (reflect-natural a var0 (keep[ a ] w)))) ⟩
  lam (reify b (x .apply (fresh[ a ] ∙ keep[ a ] w) (wk[ evalTy a ] (keep[ a ] w) (var0' a))))  ≡˘⟨ cong lam (reify-pres-≋ b (x .natural fresh[ a ] (keep[ a ] w) _)) ⟩
  lam (reify b (wk[ evalTy b ] (keep[ a ] w) (x .apply fresh[ a ] (var0' a))))                  ≡⟨  cong lam (reify-natural b _ (keep[ a ] w)) ⟩
  lam (wkNf (keep[ a ] w) (reify b (x .apply fresh[ a ] (var0' a))))                            ≡⟨⟩
  wkNf w (reify (a ⇒ b) x)                                                                      ∎
reify-natural (□ a) x w = let open ≡-Reasoning in begin
  reify (□ a) (wk[ evalTy (□ a) ] w x)                                                      ≡⟨⟩
  box (reify a (wk[ evalTy (□ a) ] w x .apply idWk new◁IS4))                                ≡⟨⟩
  box (reify a (x .apply (w ∙ idWk)                new◁IS4))                                ≡⟨  cong (λ w → box (reify a (x .apply w new◁IS4))) (rightIdWk w) ⟩
  box (reify a (x .apply w                         new◁IS4))                                ≡˘⟨ cong (λ w → box (reify a (x .apply w new◁IS4))) (leftIdWk w) ⟩
  box (reify a (x .apply (idWk ∙ w)                new◁IS4))                                ≡⟨⟩
  box (reify a (x .apply (idWk ∙ factorWk new◁IS4 (keep# w)) (factor◁ new◁IS4 (keep# w))))  ≡⟨  cong box (reify-pres-≋ a (x .natural idWk new◁IS4 (keep# w))) ⟩
  box (reify a (wk[ evalTy a ] (keep# w) (x .apply idWk new◁IS4)))                          ≡⟨  cong box (reify-natural a (x .apply idWk new◁IS4) (keep# w)) ⟩
  box (wkNf (keep# w) (reify a (x .apply idWk new◁IS4)))                                    ≡⟨⟩
  wkNf w (reify (□ a) x)                                                                    ∎

-- (reflected) identity substitution (one direction of the prinicipal lemma?)
idₛ' : (Γ : Ctx) → Sub' Γ Γ
idₛ' []       = tt
idₛ' (Γ `, a) = record { elem = (wkSub' Γ fresh[ a ] (idₛ' Γ) , (var0' a)) }
idₛ' (Γ #)    = elem (-, new◁IS4 , idₛ' Γ)
