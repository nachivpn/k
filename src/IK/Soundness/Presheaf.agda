{-# OPTIONS --allow-unsolved-metas #-}
module IK.Soundness.Presheaf where

open import Data.Unit  using (⊤ ; tt)
open import Data.Product  using (Σ ; _×_ ; _,_)
open import Relation.Binary.PropositionalEquality

open import IK.Term
open import IK.Norm
open import IK.HellOfSyntacticLemmas

postulate
  funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x) → f ≡ g

  funexti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

variable
  A B G : Ctx → Set

-- Presheaf refinement of the Tm' interpretation.
-- Used ensure that the domain of interpretation is indeed presheafs
-- (i.e., context-indexed sets with a monotonicitiy condition that *obey naturality*)
Psh : Tm' Γ a → Set
-- naturality of normal forms, wkTm w (embNf n) ≡ embNf (wkNf w n),
-- is known to be true from impl., and thus left implicit
Psh {Γ} {𝕓}     n      = ⊤
Psh {Γ} {a ⇒ b} f      = {Γ' : Ctx} (w : Γ' ≤ Γ)
  → (x : Tm' Γ' a) → Psh x
  -- naturality of exponential presheaf
  → ({Γ⁰ : Ctx} → (w' : Γ⁰ ≤ Γ') → f (w ∙ w') (wkTm' w' x) ≡ wkTm' w' (f w x))
  -- result is in Psh
    × Psh (f w x)
-- to prove Box A is a presheaf (that obeys naturality)
-- we only need to know that A is a presheaf (i.e., x obeys naturality)
Psh {Γ} {◻ a} (box x) = Psh x

-- wkTm' preserves Psh
wkTm'PresPsh : (w : Γ' ≤ Γ) (x : Tm' Γ a) → Psh x → Psh (wkTm' w x)
wkTm'PresPsh {a = 𝕓}     w x       p = tt
wkTm'PresPsh {a = a ⇒ b} w f       p = λ w' y q →
  -- nf gives us that f obeys naturality (ind. hyp enabled by PSh)
  -- pfx gives us that the codomain of f is a presheaf, i.e., `PSh (f _ x)`
  let (nf , pfx) = p (w ∙ w') y q
  in (λ {Γ⁰} w'' →
    subst (λ z → f z _ ≡ wkTm' _ _) (assocWk w w' w'') (nf w''))
    , pfx
wkTm'PresPsh {a = ◻ a}  w (box x) p = wkTm'PresPsh (keep🔒 w) x p

Pshₛ : Sub' Γ Δ → Set
-- naturality terminal presheaf left implicit
Pshₛ {Γ} {[]}     s          = ⊤
-- naturality of product preheaf left implicit
Pshₛ {Γ} {Δ `, a} (s , x)    = Pshₛ s × Psh x

Pshₛ {Γ} {Δ 🔒}    (lock s e) = Pshₛ s

-- wkSub' preserves Pshₛ
wkSub'PresPsh : (w : Γ' ≤ Γ) (s : Sub' Γ Δ) → Pshₛ s → Pshₛ (wkSub' w s)
wkSub'PresPsh {Δ = []}     w s          p         =
  tt
wkSub'PresPsh {Δ = Δ `, a} w (s , x)    (ps , px) =
  wkSub'PresPsh w s ps , wkTm'PresPsh w x px
wkSub'PresPsh {Δ = Δ 🔒}    w (lock s e) p         =
  wkSub'PresPsh (stashWk e w) s p

-----------------------------
-- Tm' and Sub' are presheafs
-----------------------------

-- identity functor law of Tm'
wkTm'PresId : (x : Tm' Γ a) → wkTm' idWk x ≡ x
wkTm'PresId {a = 𝕓}     n
  = wkNfPresId n
wkTm'PresId {a = a ⇒ b} f
  = funexti (λ _ → funext (λ _ → cong f (leftIdWk _)))
wkTm'PresId {a = ◻ a}  (box x)
  = cong box (wkTm'PresId x)

-- composition functor law of Tm'
wkTm'Pres∙ : (w : Γ' ≤ Γ) (w' : Γ'' ≤ Γ') (x : Tm' Γ a)
  → wkTm' w' (wkTm' w x) ≡ wkTm' (w ∙ w') x
wkTm'Pres∙ {a = 𝕓}     w w' n       =
  wkNfPres∙ w w' n
wkTm'Pres∙ {a = a ⇒ b} w w' f       =
  funexti (λ _ → funext (λ w'' →
    cong f (sym (assocWk w w' w''))))
wkTm'Pres∙ {a = ◻ a}  w w' (box x) =
  cong box (wkTm'Pres∙ (keep🔒 w) (keep🔒 w') x)

-- identity functor law of Sub'
wkSub'PresId : (s : Sub' Γ Δ) → wkSub' idWk s ≡ s
wkSub'PresId {Δ = []}     tt         = refl
wkSub'PresId {Δ = Δ `, a} (s , x)    = cong₂ _,_ (wkSub'PresId s) (wkTm'PresId x)
wkSub'PresId {Δ = Δ 🔒}    (lock s e) with ←🔒IsPre🔒 e | 🔒→isPost🔒 e
... | refl | refl = cong₂ lock
  (trans (cong₂ wkSub' (stashWkId e) refl) (wkSub'PresId s))
  (resExtId e)

-- composition functor law of Sub'
wkSub'Pres∙ : (w : Γ' ≤ Γ) (w' : Γ'' ≤ Γ') (s : Sub' Γ Δ)
  → wkSub' w' (wkSub' w s) ≡ wkSub' (w ∙ w') s
wkSub'Pres∙ {Δ = []}     w w' tt         = refl
wkSub'Pres∙ {Δ = Δ `, a} w w' (s , x)    = cong₂ _,_ (wkSub'Pres∙ w w' s) (wkTm'Pres∙ w w' x)
wkSub'Pres∙ {Δ = Δ 🔒}    w w' (lock s e) = cong₂ lock
  (trans  (wkSub'Pres∙ _ _ s) (cong₂ wkSub' (stashSquash w' w e) refl))
  (resAccLem w' w e)

-- naturality of substVar'
nat-substVar' : (w : Δ' ≤ Δ) (x : Var Γ a) (s : Sub' Δ Γ)
  → substVar' x (wkSub' w s) ≡ wkTm' w (substVar' x s)
nat-substVar' w ze     s       = refl
nat-substVar' w (su x) (s , _) = nat-substVar' w x s

-- substVar' obeys Psh
psh-substVar' : (x : Var Γ a) (s : Sub' Δ Γ) → Pshₛ s → Psh (substVar' x s)
psh-substVar' ze     (_ , x) (_ , px) = px
psh-substVar' (su x) (s , _) (ps , _) = psh-substVar' x s ps

-- eval obeys Psh
psh-eval  : (t : Tm Γ a) (s : Sub' Δ Γ) → Pshₛ s → Psh (eval t s)
-- naturality of eval
nat-eval : (w : Δ' ≤ Δ) (t : Tm Γ a) (s : Sub' Δ Γ)
  → eval t (wkSub' w s) ≡ wkTm' w (eval t s)

-- WIP!
psh-eval (var x)           s         ps
  = psh-substVar' x s ps
psh-eval (lam t)           s         ps
  = λ w x px →  {!!}
psh-eval (app t u)         s         ps
  = let (_ , fxp) = psh-eval t s ps idWk _ (psh-eval u s ps) in fxp
psh-eval (box t)           s         ps
  = psh-eval t (lock s nil) ps
psh-eval (unbox t nil)     (lock s e') ps with eval t s | psh-eval t s ps
... | box x | px
  = wkTm'PresPsh (wᵣ e') x px
psh-eval (unbox t (ext e)) (s , _)  (ps , _)
  = psh-eval (unbox t e) s ps

-- WIP!
nat-eval w (var x)           s
  = nat-substVar' w x s
nat-eval w (lam t)           s
  = {!!}
nat-eval w (app t u)         s
  = {!!}
nat-eval w (box t)           s
  = cong box (nat-eval (keep🔒 w) t (lock s nil))
nat-eval w (unbox t nil)     (lock s e')
  = {!!}
nat-eval w (unbox t (ext e)) (s , _)
  = nat-eval w (unbox t e) s
