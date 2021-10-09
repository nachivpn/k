{-# OPTIONS --allow-unsolved-metas #-}
module IS4.NbE.Reification where

open import Data.Unit    using (⊤; tt)          renaming ()
open import Data.Product using (Σ; ∃; _,_; -,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; module ≡-Reasoning)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import IS4.NbE.Model

open import IS4.Term

reflect : (a : Ty) → (n : Ne  Γ a) → Ty' Γ a
reify   : (a : Ty) → (x : Ty' Γ a) → Nf  Γ a

-- interpretation of neutrals
reflect 𝕓       n = n
reflect (a ⇒ b) n = elem (λ e x → reflect b (app (wkNe e n) (reify a x))) {!!} {!!}
reflect (◻ a)   n = λ r → let (_ , e) = r in reflect a (unbox n e)

-- reify values to normal forms
reify 𝕓       n = up𝕓 n
reify (a ⇒ b) f = lam (reify b (f .apply (fresh {a = a}) (reflect a var0)))
reify (◻ a)   g = box (reify a (g (-, new)))

reify-pres-≋ : ∀ (a : Ty) {x x' : Ty' Γ a} (x≋x' : x ≋[ evalTy a ] x') → reify a x ≡ reify a x'
reify-pres-≋ 𝕓       x≋x' = cong up𝕓 x≋x'
reify-pres-≋ (a ⇒ b) x≋x' = cong lam (reify-pres-≋ b (x≋x' .pw (fresh {a = a}) (reflect a var0)))
reify-pres-≋ (◻ a)   x≋x' = cong box (reify-pres-≋ a (x≋x' refl))

reify-natural : ∀ (a : Ty) (x : Ty' Γ a) (w : Γ ⊆ Γ') → reify a (wk[ evalTy a ] w x) ≡ wkNf w (reify a x)
reify-natural 𝕓 x w = refl
reify-natural (a ⇒ b) x w = let open ≡-Reasoning in begin
  reify (a ⇒ b) (wk[ evalTy (a ⇒ b) ] w x)                                                                      ≡⟨⟩
  lam (reify b (x .apply (w ∙ fresh {a = a}) (reflect a var0)))                                                 ≡⟨ {!!} ⟩
  lam (reify b (x .apply (fresh {a = a} ∙ keep {a = a} w) (reflect a (wkNe (keep {a = a} w) var0))))            ≡⟨ {!!} ⟩
  lam (reify b (x .apply (fresh {a = a} ∙ keep {a = a} w) (wk[ evalTy a ] (keep {a = a} w) (reflect a var0))))  ≡⟨ {!!} ⟩
  lam (reify b (wk[ evalTy b ] (keep {a = a} w) (x .apply (fresh {a = a}) (reflect a var0))))                   ≡⟨ {!!} ⟩
  lam (wkNf (keep {a = a} w) (reify b (x .apply (fresh {a = a}) (reflect a var0))))                             ≡⟨⟩
  wkNf w (reify (a ⇒ b) x)                                                                                      ∎
reify-natural (◻ a) x w = {!!}

-- (reflected) identity substitution (one direction of the prinicipal lemma?)
idₛ' : (Γ : Ctx) → Ctx' Γ Γ
idₛ' []       = tt
idₛ' (Γ `, a) = record { elem = (wkCtx' {Δ = Γ} (fresh {a = a}) (idₛ' Γ) , reflect a var0) }
idₛ' (Γ 🔒)    = elem (-, (-, new) , idₛ' Γ)
