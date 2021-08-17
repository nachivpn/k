module IK.Soundness.HellOfSemanticLemmas where

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality

import Context
open import IK.Term
open import IK.Norm
open import IK.HellOfSyntacticLemmas

postulate
  funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x) → f ≡ g

  funexti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g
          
-- semantic counterpart of trimSub
trimSub' : Γ' ≤ Γ → Sub'- Γ' →̇ Sub'- Γ
trimSub' base      tt         = tt
trimSub' (drop w)  (s , _)    = trimSub' w s
trimSub' (keep w)  (s , x)    = trimSub' w s , x
trimSub' (keep🔒 w) (lock s e) = lock (trimSub' w s) e

-- naturality of trimSub'
nat-trimSub' : (w' : Δ ≤ Δ') (w : Γ' ≤ Γ) (s : Sub' Γ Δ)
  → trimSub' w' (wkSub' w s) ≡ wkSub' w (trimSub' w' s)
nat-trimSub' base       w s          = refl
nat-trimSub' (drop w')  w (s , _)    = nat-trimSub' w' w s
nat-trimSub' (keep w')  w (s , x)    = cong₂ _,_ (nat-trimSub' w' w s) refl
nat-trimSub' (keep🔒 w') w (lock s e) = cong₂ lock (nat-trimSub' w' (sliceLeft e w) s) refl

-- trimSub' preserves identity
trimSub'PresId : (s : Sub' Γ Δ) → trimSub' idWk s ≡ s
trimSub'PresId {Δ = []}     tt         = refl
trimSub'PresId {Δ = Δ `, _} (s , _)    = cong₂ _,_ (trimSub'PresId s) refl
trimSub'PresId {Δ = Δ 🔒}    (lock s e) = cong₂ lock (trimSub'PresId s) refl

-- semantic counterpart of coh-trimSub-wkVar in Substitution.agda
coh-trimSub'-wkVar' : (w : Γ' ≤ Γ) (s : Sub' Δ Γ') (x : Var Γ a)
  → substVar' (wkVar w x) s ≡ substVar' x (trimSub' w s)
coh-trimSub'-wkVar' (drop w) (s , _) ze     = coh-trimSub'-wkVar' w s ze
coh-trimSub'-wkVar' (drop w) (s , _) (su x) = coh-trimSub'-wkVar' w s (su x)
coh-trimSub'-wkVar' (keep w) (s , _) ze     = refl
coh-trimSub'-wkVar' (keep w) (s , _) (su x) = coh-trimSub'-wkVar' w s x

-- semantic counterpart of coh-trimSub-wkTm in HellOfSyntacticLemmas.agda
coh-trimSub'-wkTm : (w : Γ' ≤ Γ) (s : Sub' Δ Γ') (t : Tm Γ a)
  → eval (wkTm w t) s ≡ eval t (trimSub' w s)
coh-trimSub'-wkTm w s (var x)
  = coh-trimSub'-wkVar' w s x
coh-trimSub'-wkTm w s (lam t)
  = funexti (λ _ → funext (λ w' → funext (λ x →
      trans
        (coh-trimSub'-wkTm (keep w) (wkSub' w' s , x) t)
        (cong (λ z → eval t (z , x)) (nat-trimSub' w w' s)))))
coh-trimSub'-wkTm w s (app t u)
  = trans
      (cong (λ f → f idWk (eval (wkTm w u) s)) (coh-trimSub'-wkTm w s t))
      (cong (eval t (trimSub' w s) idWk) (coh-trimSub'-wkTm w s u))
coh-trimSub'-wkTm w s (box t)
  = cong box (coh-trimSub'-wkTm (keep🔒 w) (lock s nil) t)
coh-trimSub'-wkTm (drop w) (s , _) (unbox t e)
  = coh-trimSub'-wkTm w s (unbox t e)
coh-trimSub'-wkTm (keep🔒 w) (lock s e) (unbox t nil)
  = cong₂ unbox' (coh-trimSub'-wkTm w s t) refl
coh-trimSub'-wkTm (keep w) (s , _) (unbox t (ext e))
  = coh-trimSub'-wkTm w s (unbox t e)

-- semantic counterpart of coh-trimSub-wkSub in `HellOfSyntacticLemmas.agda`
coh-trimSub'-wkSub : (w : Γ' ≤ Γ) (s : Sub Γ Δ) (s' : Sub' Δ' Γ')
  → evalₛ (wkSub w s) s' ≡ evalₛ s (trimSub' w s')
coh-trimSub'-wkSub w [] s'
  = refl
coh-trimSub'-wkSub w (s `, t) s'
  = cong₂ _,_ (coh-trimSub'-wkSub w s s') (coh-trimSub'-wkTm w s' t)
coh-trimSub'-wkSub (drop w) (lock s e) (s' , _)
  = coh-trimSub'-wkSub w (lock s e) s'
coh-trimSub'-wkSub (keep w) (lock s (ext e)) (s' , _)
  = coh-trimSub'-wkSub w (lock s e) s'
coh-trimSub'-wkSub (keep🔒 w) (lock s nil) (lock s' e')
  = cong₂ lock (coh-trimSub'-wkSub w s s') refl

-- evalₛ preserves identity
evalₛPresId : (s' : Sub' Γ Δ) → evalₛ idₛ s' ≡ s'
evalₛPresId {Δ = []}     tt
  = refl
evalₛPresId {Δ = Δ `, _} (s' , x)
  = cong₂ (_,_)
          (trans
            (coh-trimSub'-wkSub fresh idₛ (s' , x))
            (trans
              (cong (evalₛ idₛ) (trimSub'PresId s'))
              (evalₛPresId s')))
          refl
evalₛPresId {Δ = Δ 🔒} (lock s' e)
  = cong₂ lock (evalₛPresId s') refl
