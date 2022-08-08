{-# OPTIONS --safe --without-K #-}
module Type.Properties where

open import Relation.Nullary using (_because_; yes; no)

open import Relation.Binary.Definitions           using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import Type.Base

Ty-Decidable : Decidable (_≡_ {A = Ty})
Ty-Decidable ι       ι       = yes refl
Ty-Decidable ι       (a ⇒ b) = no  λ ()
Ty-Decidable ι       (□ a)   = no  λ ()
Ty-Decidable (a ⇒ b) ι       = no  λ ()
Ty-Decidable (a ⇒ b) (c ⇒ d) with Ty-Decidable a c | Ty-Decidable b d
... | yes a≡c  | yes b≡d     = yes (cong₂ _⇒_ a≡c b≡d)
... | yes a≡c  | no  ¬b≡d    = no  λ { refl → ¬b≡d refl }
... | no  ¬a≡c | yes b≡d     = no  λ { refl → ¬a≡c refl }
... | no  ¬a≡c | no  ¬b≡d    = no  λ { refl → ¬a≡c refl }
Ty-Decidable (a ⇒ b) (□ c)   = no  λ ()
Ty-Decidable (□ a)   ι       = no  λ ()
Ty-Decidable (□ a)   (b ⇒ c) = no  λ ()
Ty-Decidable (□ a)   (□ b)   with Ty-Decidable a b
... | yes a≡b                = yes (cong □_ a≡b)
... | no  ¬a≡b               = no  λ { refl → ¬a≡b refl }
