{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Context.Properties (Ty : Set) (Ty-Decidable : Decidable (_≡_ {A = Ty})) where

open import Data.Empty
  using (⊥ ; ⊥-elim)

open import Relation.Nullary
  using (_because_ ; yes ; no)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; subst ; subst₂ ; cong ; cong₂)

open import Context.Base Ty

open import PEUtil

private
  variable
    a b c d : Ty

-----------
-- Contexts
-----------

Ctx-Decidable : Decidable (_≡_ {A = Ctx})
Ctx-Decidable []       []       = yes refl
Ctx-Decidable []       (Γ `, a) = no  λ ()
Ctx-Decidable []       (Γ #)    = no  λ ()
Ctx-Decidable (Γ `, a) []       = no  λ ()
Ctx-Decidable (Γ `, a) (Δ `, b) with Ctx-Decidable Γ Δ | Ty-Decidable a b
... | yes Γ≡Δ  | yes a≡b        = yes (cong₂ _`,_ Γ≡Δ a≡b)
... | yes Γ≡Δ  | no  ¬a≡b       = no  λ { refl → ¬a≡b refl }
... | no  ¬Γ≡Δ | yes a≡b        = no  λ { refl → ¬Γ≡Δ refl }
... | no  ¬Γ≡Δ | no  ¬a≡b       = no  λ { refl → ¬a≡b refl }
Ctx-Decidable (Γ `, a) (Δ #)    = no  λ ()
Ctx-Decidable (Γ #)   []        = no  λ ()
Ctx-Decidable (Γ #)   (Δ `, a)  = no  λ ()
Ctx-Decidable (Γ #)   (Δ #)     with Ctx-Decidable Γ Δ
... | yes Γ≡Δ                   = yes (cong _# Γ≡Δ)
... | no  ¬Γ≡Δ                  = no  λ { refl → ¬Γ≡Δ refl }

open Decidable⇒K Ctx-Decidable public
  using    ()
  renaming (Decidable⇒K to Ctx-K ; Decidable⇒UIP to Ctx-irrelevant)

`,-injective-left : Γ `, a ≡ Δ `, b → Γ ≡ Δ
`,-injective-left refl = refl

`,-injective-right : Γ `, a ≡ Δ `, b → a ≡ b
`,-injective-right refl = refl

#-injective : Γ # ≡ Δ # → Γ ≡ Δ
#-injective refl = refl

private
  open import Data.Nat
  open import Data.Nat.Properties

  m≢n+1+m : ∀ m {n} → m ≢ n + suc m
  m≢n+1+m m m≡n+1+m = m≢1+m+n m (trans m≡n+1+m (+-comm _ (suc m)))

  length : (Γ : Ctx) → ℕ
  length []       = 0
  length (Γ `, a) = 1 + length Γ
  length (Γ #)    = 1 + length Γ

  lengthPres+ : ∀ Γ Δ → length (Γ ,, Δ) ≡ length Δ + length Γ
  lengthPres+ Γ []       = refl
  lengthPres+ Γ (Δ `, a) = cong suc (lengthPres+ Γ Δ)
  lengthPres+ Γ (Δ #)    = cong suc (lengthPres+ Γ Δ)

module _ {A : Set} where
  Γ≡Γ,a-impossible₁ : Γ ≡ Γ `, a ,, Γ' → A
  Γ≡Γ,a-impossible₁ {Γ} {a} {Γ'} p = ⊥-elim (m≢n+1+m (length Γ) (trans (cong length p) (lengthPres+ (Γ `, a) Γ')))

  Γ≡Γ,a-impossible₂ : Γ ≡ Γ ,, Γ' `, a → A
  Γ≡Γ,a-impossible₂ {Γ} {Γ'} {a} p = ⊥-elim (m≢1+n+m (length Γ) (trans (cong length p) (cong suc (lengthPres+ Γ Γ'))))

  Γ≡Γ#-impossible₁ : Γ ≡ Γ # ,, Γ' → A
  Γ≡Γ#-impossible₁ {Γ} {Γ'} p = ⊥-elim (m≢n+1+m (length Γ) (trans (cong length p) (lengthPres+ (Γ #) Γ')))

  Γ≡Γ#-impossible₂ : Γ ≡ (Γ ,, Γ') # → A
  Γ≡Γ#-impossible₂ {Γ} {Γ'} p = ⊥-elim (m≢1+n+m (length Γ) (trans (cong length p) (cong suc (lengthPres+ Γ Γ'))))

,,-injective-right : Δ ,, Γ ≡ Δ ,, Γ' → Γ ≡ Γ'
,,-injective-right {Δ} {[]}     {[]}      p = refl
,,-injective-right {Δ} {[]}     {Γ' `, a} p = Γ≡Γ,a-impossible₂ p
,,-injective-right {Δ} {[]}     {Γ' #}    p = Γ≡Γ#-impossible₂ p
,,-injective-right {Δ} {Γ `, a} {[]}      p = Γ≡Γ,a-impossible₂ (sym p)
,,-injective-right {Δ} {Γ `, a} {Γ' `, b} p = cong₂ _`,_ (,,-injective-right (`,-injective-left p)) (`,-injective-right p)
,,-injective-right {Δ} {Γ #}   {[]}       p = Γ≡Γ#-impossible₂ (sym p)
,,-injective-right {Δ} {Γ #}   {Γ' #}     p = cong _# (,,-injective-right (#-injective p))

,,-assoc : (ΓLL ,, ΓLR) ,, ΓR ≡ ΓLL ,, (ΓLR ,, ΓR)
,,-assoc {ΓLL} {ΓLR} {[]}      = refl
,,-assoc {ΓLL} {ΓLR} {ΓR `, a} = cong (_`, a) (,,-assoc {ΓLL} {ΓLR})
,,-assoc {ΓLL} {ΓLR} {ΓR #}    = cong _#      (,,-assoc {ΓLL} {ΓLR})

,,-leftUnit : {Γ : Ctx} → [] ,, Γ ≡ Γ
,,-leftUnit {[]}     = refl
,,-leftUnit {Γ `, a} = cong (_`, _) ,,-leftUnit
,,-leftUnit {Γ #}    = cong _# ,,-leftUnit
