{-# OPTIONS --without-K #-}
module IK.Norm.NbE.Model where

open import Data.Unit    using (⊤ ; tt)
open import Data.Product using (Σ ; _×_ ; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; refl ; sym ; trans ; cong ; cong₂)

open import IK.Term

open import FunExt

------------
-- NbE Model
------------

-- family of maps between interpretations
_→̇_ : (Ctx → Set) → (Ctx → Set) → Set
_→̇_ A B = {Δ : Ctx} → A Δ → B Δ

-- semantic counterpart of `box` from `Tm`
record Box (A : Ctx → Set) (Γ : Ctx) : Set where
  constructor box'
  field
    unbox' : A (Γ #)

-- semantic counterpart of `lock` from `Sub`
data Lock (A : Ctx → Set) : Ctx → Set where
  lock : A ΓL → LFExt Γ (ΓL #) ΓR  → Lock A Γ
  -- equivalently, `lock : #-free Γ' → A Γ → Lock A (Γ # ,, Γ')`

-- interpretation of types
Tm' : Ctx → Ty → Set
Tm' Γ ι       = Nf Γ ι
Tm' Γ (a ⇒ b) = {Γ' : Ctx} → Γ ⊆ Γ' → (Tm' Γ' a → Tm' Γ' b)
Tm' Γ (□ a)   = Box (λ Γ' → Tm' Γ' a) Γ

Tm'- : Ty → Ctx → Set
Tm'- a Γ = Tm' Γ a

-- interpretation of contexts
Sub' : Ctx → Ctx → Set
Sub' Δ []       = ⊤
Sub' Δ (Γ `, a) = Sub' Δ Γ × Tm' Δ a
Sub' Δ (Γ #)    = Lock (λ Γ' → Sub' Γ' Γ) Δ

Sub'- : Ctx → Ctx → Set
Sub'- Δ Γ = Sub' Γ Δ

-- values in the model can be weakened
wkTm' : Γ ⊆ Γ' → Tm' Γ a → Tm' Γ' a
wkTm' {a = ι}     e n = wkNf e n
wkTm' {a = a ⇒ b} e f = λ e' y → f (e ∙ e') y
wkTm' {a = □ a}   e b = let box' x = b in box' (wkTm' (keep# e) x)

-- substitutions in the model can be weakened
wkSub' : Γ ⊆ Γ' → Sub' Γ Δ → Sub' Γ' Δ
wkSub' {Δ = []}     w tt         = tt
wkSub' {Δ = Δ `, a} w (s , x)    = wkSub' w s , wkTm' w x
wkSub' {Δ = Δ #}    w (lock s e) = lock (wkSub' (sliceLeft e w) s) (wkLFExt e w)

-- semantic counterpart of `unbox` from `Tm`
unbox' : Box (λ Δ → Tm' Δ a) ΓL → LFExt Γ (ΓL #) ΓR → Tm' Γ a
unbox' b e = let box' x = b in wkTm' (LFExtToWk e) x

unlock' : Sub' Δ (Γ #) → Σ (Ctx × Ctx) λ { (ΔL , ΔR) → Sub' ΔL Γ × LFExt Δ (ΔL #) ΔR }
unlock' (lock γ e) = _ , γ , e

-- interpretation of variables
substVar' : Var Γ a → (Sub'- Γ →̇ Tm'- a)
substVar' zero     (_ , x) = x
substVar' (succ v) (γ , _) = substVar' v γ

LFExt' : LFExt Γ (ΓL #) ΓR → Sub'- Γ →̇ Sub'- (ΓL #)
LFExt' nil     γ       = γ          -- = id
LFExt' (ext e) (γ , _) = LFExt' e γ -- = LFExt' e ∘ π₁

-- interpretation of terms
eval : Tm Γ a → (Sub'- Γ →̇ Tm'- a)
eval (var   v)   s = substVar' v s
eval (lam   t)   s = λ e x → eval t (wkSub' e s , x)
eval (app   t u) s = (eval t s) idWk (eval u s)
eval (box   t)   s = box' (eval t (lock s new))
eval (unbox t e) s = let (_ , s' , e') = unlock' (LFExt' e s) in unbox' (eval t s') e' -- = ^(eval t) ∘ LFExt' e

-- interpretation of substitutions (simply "do everything pointwise")
evalₛ : Sub Γ Δ → Sub'- Γ  →̇ Sub'- Δ
evalₛ []         γ = tt
evalₛ (s `, t)   γ = evalₛ s γ , eval t γ
evalₛ (lock s e) γ = let (_ , γ' , e') = unlock' (LFExt' e γ) in lock (evalₛ s γ') e' -- = Lock (evalₛ s ∘ LFExt' e)

-----------------------------
-- Presheaf refinement of Tm'
-----------------------------

-- Used to ensure that the domain of interpretation is indeed presheafs
Psh : Tm' Γ a → Set
Psh {Γ} {ι}     n = ⊤
Psh {Γ} {a ⇒ b} f = ∀ {Γ' : Ctx} (w : Γ ⊆ Γ')
  → (x : Tm' Γ' a) → Psh x
  -- naturality of presheaf exponentials
  → ({Γ⁰ : Ctx} → (w' : Γ' ⊆ Γ⁰) → f (w ∙ w') (wkTm' w' x) ≡ wkTm' w' (f w x))
    × Psh (f w x)
Psh {Γ} {□ a}   b = let box' x = b in Psh x

-- Psh extended to interpretation of contexts
Pshₛ : Sub' Γ Δ → Set
Pshₛ {Γ} {[]}     tt         = ⊤
Pshₛ {Γ} {Δ `, a} (s , x)    = Pshₛ s × Psh x
Pshₛ {Γ} {Δ #}    (lock s e) = Pshₛ s

-----------------------------------
-- Psh(ₛ) is preserved by weakening
-----------------------------------

-- wkTm' preserves Psh
wkTm'PresPsh : (w : Γ ⊆ Γ') (x : Tm' Γ a) → Psh x → Psh (wkTm' w x)
wkTm'PresPsh {a = ι}     w n p = tt
wkTm'PresPsh {a = a ⇒ b} w f p = λ w' y q →
  -- nf gives us that f obeys naturality (ind. hyp enabled by PSh)
  -- pfx gives us that the codomain of f is a presheaf, i.e., `PSh (f _ x)`
  let (nf , pfx) = p (w ∙ w') y q
  in (λ {Γ⁰} w'' →
    subst (λ z → f z _ ≡ wkTm' _ _) (assocWk w w' w'') (nf w''))
    , pfx
wkTm'PresPsh {a = □ a}   w b p = let box' x = b in wkTm'PresPsh (keep# w) x p

-- wkSub' preserves Pshₛ
wkSub'PresPsh : (w : Γ ⊆ Γ') (s : Sub' Γ Δ) → Pshₛ s → Pshₛ (wkSub' w s)
wkSub'PresPsh {Δ = []}     w s          p         =
  tt
wkSub'PresPsh {Δ = Δ `, a} w (s , x)    (ps , px) =
  wkSub'PresPsh w s ps , wkTm'PresPsh w x px
wkSub'PresPsh {Δ = Δ #}    w (lock s e) p         =
  wkSub'PresPsh (sliceLeft e w) s p

-------------------------
-- `Tm'- a` is a presheaf
-------------------------

-- Given `a : Ty`,
-- (object map)   Tm'- a : Ctx → Set
-- (morphism map) wkTm'  : Γ' ≤ Γ → Tm'- a Γ → Tm'- a Γ'

-- identity functor law of `Tm'- a`
wkTm'PresId : (x : Tm' Γ a) → wkTm' idWk x ≡ x
wkTm'PresId {a = ι}     n
  = wkNfPresId n
wkTm'PresId {a = a ⇒ b} f
  = funexti' (λ _ → funext (λ _ → cong f (leftIdWk _)))
wkTm'PresId {a = □ a}   b
  = let box' x = b in cong box' (wkTm'PresId x)

-- composition functor law of `Tm'- a`
wkTm'Pres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (x : Tm' Γ a)
  → wkTm' w' (wkTm' w x) ≡ wkTm' (w ∙ w') x
wkTm'Pres∙ {a = ι}     w w' n
  = wkNfPres∙ w w' n
wkTm'Pres∙ {a = a ⇒ b} w w' f
  = funexti' (λ _ → funext (λ w'' →
    cong f (sym (assocWk w w' w''))))
wkTm'Pres∙ {a = □ a}   w w' b
  = let box' x = b in cong box' (wkTm'Pres∙ (keep# w) (keep# w') x)

--------------------------
-- `Sub'- Δ` is a presheaf
--------------------------

-- Given `Δ : Ctx`,
-- (object map)   Sub'- Δ : Ctx → Set
-- (morphism map) wkSub'  : Γ' ≤ Γ → Sub'- Δ Γ → Sub'- Δ Γ'

-- identity functor law of `Sub'- Γ`
wkSub'PresId : (s : Sub' Γ Δ) → wkSub' idWk s ≡ s
wkSub'PresId {Δ = []}     tt         = refl
wkSub'PresId {Δ = Δ `, a} (s , x)    = cong₂ _,_ (wkSub'PresId s) (wkTm'PresId x)
wkSub'PresId {Δ = Δ #}    (lock s e) with ←#IsPre# e | #→IsPost# e
... | refl | refl = cong₂ lock
  (trans (cong₂ wkSub' (sliceLeftId e) refl) (wkSub'PresId s))
  (wkLFExtPresId e)

-- composition functor law of `Sub'- Γ`
wkSub'Pres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (s : Sub' Γ Δ)
  → wkSub' w' (wkSub' w s) ≡ wkSub' (w ∙ w') s
wkSub'Pres∙ {Δ = []}     w w' tt         = refl
wkSub'Pres∙ {Δ = Δ `, a} w w' (s , x)    = cong₂ _,_ (wkSub'Pres∙ w w' s) (wkTm'Pres∙ w w' x)
wkSub'Pres∙ {Δ = Δ #}    w w' (lock s e) = cong₂ lock
  (trans  (wkSub'Pres∙ _ _ s) (cong₂ wkSub' (sliceLeftPres∙ w w' e) refl))
  (wkLFExtPres∙ w w' e)

-------------------------------------------
-- `subsVar' x` is a natural transformation
-------------------------------------------

-- for `v : Var Γ a`,
-- substVar v : Sub'- Γ →̇ Tm'- a

-- naturality of substVar'
nat-substVar' : (w : Δ ⊆ Δ') (x : Var Γ a) (s : Sub' Δ Γ)
  → substVar' x (wkSub' w s) ≡ wkTm' w (substVar' x s)
nat-substVar' w zero     s       = refl
nat-substVar' w (succ v) (s , _) = nat-substVar' w v s

-- substVar' obeys Psh
psh-substVar' : (x : Var Γ a) (s : Sub' Δ Γ) → Pshₛ s → Psh (substVar' x s)
psh-substVar' zero     (_ , x) (_ , px) = px
psh-substVar' (succ v) (s , _) (ps , _) = psh-substVar' v s ps

---------------------------------------
-- `eval t` is a natural transformation
---------------------------------------

-- for `t : Tm Γ a`,
-- eval t : Sub'- Γ →̇ Tm'- a

-- (mutually defined functions below)

-- result of evaluation is in Psh
psh-eval  : (t : Tm Γ a) (s : Sub' Δ Γ)
  → Pshₛ s → Psh (eval t s)
-- naturality of `eval t`
nat-eval : (t : Tm Γ a) (w : Δ ⊆ Δ') (s : Sub' Δ Γ)
  → Pshₛ s → eval t (wkSub' w s) ≡ wkTm' w (eval t s)

-- psh-eval
psh-eval (var v)           s           ps
  = psh-substVar' v s ps
psh-eval (lam t)           s           ps
  = λ w x px
    → (λ w' → trans
         -- rewrite using wkSub'Pres∙
         (cong (λ z → (eval t (z , _))) (sym (wkSub'Pres∙ w w' s)))
         -- follows directly from nat-eval
         (nat-eval t w' (wkSub' w s , x) (wkSub'PresPsh w s ps , px)))
      , (psh-eval t _ (wkSub'PresPsh w s ps , px))
psh-eval (app t u)         s           ps
  = let (_ , fxp) = psh-eval t s ps idWk _ (psh-eval u s ps) in fxp
psh-eval (box t)           s           ps
  = psh-eval t (lock s new) ps
psh-eval (unbox t nil)     (lock s e') ps with eval t s | psh-eval t s ps
... | b | px
  = let box' x = b in wkTm'PresPsh (LFExtToWk e') x px
psh-eval (unbox t (ext e)) (s , _)     (ps , _)
  = psh-eval (unbox t e) s ps

-- nat-eval
nat-eval (var v)           w s          ps
  = nat-substVar' w v s
nat-eval (lam t)           w s          ps
  = funexti' (λ _ → funext λ _ → funext (λ _
    → cong (λ z →  eval t (z , _)) (wkSub'Pres∙ _ _ _)))
nat-eval (app t u)         w s          ps with
  (psh-eval t s ps idWk (eval u s) (psh-eval u s ps))
... | (g , _)
  rewrite nat-eval t w s ps | nat-eval u w s ps
  = trans
    (cong
      (λ z → eval t s z (wkTm' w (eval u s)))
      (trans (rightIdWk w) (sym (leftIdWk w))))
    (g  w)
nat-eval (box t)           w s          ps
  = cong box' (nat-eval t (keep# w) (lock s new) ps)
nat-eval (unbox t nil)     w (lock s e) ps = trans
  (cong (λ z → unbox' z (wkLFExt e w)) (nat-eval t (sliceLeft e w) s ps))
  (gsLemma w e (eval t s))
  where
  gsLemma : (w : Δ ⊆ Δ') (e : LFExt Δ (ΓL #) ΓR) (x : Tm' ΓL (□ a))
    → unbox' (wkTm' (sliceLeft e w) x) (wkLFExt e w) ≡ wkTm' w (unbox' x e)
  gsLemma w e b = let box' x = b in trans (wkTm'Pres∙ _ _ _)
    (sym (trans
      (wkTm'Pres∙ _ _ _)
      (cong (λ z → wkTm' z x) (slicingLemma w e))))
nat-eval (unbox t (ext e)) w (s , _)    (ps , _)
  = nat-eval (unbox t e) w s ps

---------------------------------------
-- `evalₛ s` is a natural transformation
---------------------------------------

-- for `s : Sub Γ Δ`,
-- evalₛ s : Sub'- Γ  →̇ Sub'- Δ

psh-evalₛ : (s : Sub Γ Γ') (s' : Sub' Δ Γ)
    → Pshₛ s' → Pshₛ (evalₛ s s')
psh-evalₛ []               s'          ps'
  = tt
psh-evalₛ (s `, t)         s'          ps'
  = (psh-evalₛ s s' ps') , (psh-eval t s' ps')
psh-evalₛ (lock s nil)     (lock s' e) ps'
  = psh-evalₛ s s' ps'
psh-evalₛ (lock s (ext e)) (s' , _)    (ps' , _)
  = psh-evalₛ (lock s e) s' ps'

-- naturality of evalₛ
nat-evalₛ : (w : Δ ⊆ Δ')  (s : Sub Γ' Γ) (s' : Sub' Δ Γ') (ps' : Pshₛ s')
  → evalₛ s (wkSub' w s') ≡ wkSub' w (evalₛ s s')
nat-evalₛ w []               s'          ps'
  = refl
nat-evalₛ w (s `, t)         s'          ps'
  = cong₂ _,_ (nat-evalₛ w s s' ps') (nat-eval t w s' ps')
nat-evalₛ w (lock s nil)     (lock s' e) ps'
  = cong₂ lock (nat-evalₛ (sliceLeft e w) s s' ps') refl
nat-evalₛ w (lock s (ext e)) (s' , _)    (ps' , _)
  = nat-evalₛ w (lock s e) s' ps'

-- semantic counterpart of trimSub
trimSub' : Γ ⊆ Γ' → Sub'- Γ' →̇ Sub'- Γ
trimSub' base      tt         = tt
trimSub' (drop w)  (s , _)    = trimSub' w s
trimSub' (keep w)  (s , x)    = trimSub' w s , x
trimSub' (keep# w) (lock s e) = lock (trimSub' w s) e

-- naturality of trimSub'
nat-trimSub' : (w' : Δ' ⊆ Δ) (w : Γ ⊆ Γ') (s : Sub' Γ Δ)
  → trimSub' w' (wkSub' w s) ≡ wkSub' w (trimSub' w' s)
nat-trimSub' base       w tt         = refl
nat-trimSub' (drop  w') w (s , _)    = nat-trimSub' w' w s
nat-trimSub' (keep  w') w (s , x)    = cong₂ _,_ (nat-trimSub' w' w s) refl
nat-trimSub' (keep# w') w (lock s e) = cong₂ lock (nat-trimSub' w' (sliceLeft e w) s) refl

-- trimSub' preserves identity
trimSub'PresId : (s : Sub' Γ Δ) → trimSub' idWk s ≡ s
trimSub'PresId {Δ = []}     tt         = refl
trimSub'PresId {Δ = Δ `, _} (s , _)    = cong₂ _,_ (trimSub'PresId s) refl
trimSub'PresId {Δ = Δ #}    (lock s e) = cong₂ lock (trimSub'PresId s) refl

-- semantic counterpart of coh-trimSub-wkVar in Substitution.agda
coh-trimSub'-wkVar' : (w : Γ ⊆ Γ') (s : Sub' Δ Γ') (x : Var Γ a)
  → substVar' (wkVar w x) s ≡ substVar' x (trimSub' w s)
coh-trimSub'-wkVar' (drop w) (s , _) zero     = coh-trimSub'-wkVar' w s zero
coh-trimSub'-wkVar' (drop w) (s , _) (succ v) = coh-trimSub'-wkVar' w s (succ v)
coh-trimSub'-wkVar' (keep w) (s , _) zero     = refl
coh-trimSub'-wkVar' (keep w) (s , _) (succ v) = coh-trimSub'-wkVar' w s v

-- semantic counterpart of coh-trimSub-wkTm in HellOfSyntacticLemmas.agda
coh-trimSub'-wkTm : (w : Γ ⊆ Γ') (s : Sub' Δ Γ') (t : Tm Γ a)
  → eval (wkTm w t) s ≡ eval t (trimSub' w s)
coh-trimSub'-wkTm w         s          (var v)
  = coh-trimSub'-wkVar' w s v
coh-trimSub'-wkTm w         s          (lam t)
  = funexti' (λ _ → funext (λ w' → funext (λ x →
      trans
        (coh-trimSub'-wkTm (keep w) (wkSub' w' s , x) t)
        (cong (λ z → eval t (z , x)) (nat-trimSub' w w' s)))))
coh-trimSub'-wkTm w         s          (app t u)
  = trans
      (cong (λ f → f idWk (eval (wkTm w u) s)) (coh-trimSub'-wkTm w s t))
      (cong (eval t (trimSub' w s) idWk) (coh-trimSub'-wkTm w s u))
coh-trimSub'-wkTm w s (box t)
  = cong box' (coh-trimSub'-wkTm (keep# w) (lock s new) t)
coh-trimSub'-wkTm (drop w)  (s , _)    (unbox t e)
  = coh-trimSub'-wkTm w s (unbox t e)
coh-trimSub'-wkTm (keep w)  (s , _)    (unbox t (ext e))
  = coh-trimSub'-wkTm w s (unbox t e)
coh-trimSub'-wkTm (keep# w) (lock s e) (unbox t nil)
  = cong (λ b → unbox' b e) (coh-trimSub'-wkTm w s t)

-- semantic counterpart of coh-trimSub-wkSub in `HellOfSyntacticLemmas.agda`
coh-trimSub'-wkSub : (w : Γ ⊆ Γ') (s : Sub Γ Δ) (s' : Sub' Δ' Γ')
  → evalₛ (wkSub w s) s' ≡ evalₛ s (trimSub' w s')
coh-trimSub'-wkSub w        []               s'
  = refl
coh-trimSub'-wkSub w        (s `, t)         s'
  = cong₂ _,_ (coh-trimSub'-wkSub w s s') (coh-trimSub'-wkTm w s' t)
coh-trimSub'-wkSub (drop w) (lock s e)       (s' , _)
  = coh-trimSub'-wkSub w (lock s e) s'
coh-trimSub'-wkSub (keep w) (lock s (ext e)) (s' , _)
  = coh-trimSub'-wkSub w (lock s e) s'
coh-trimSub'-wkSub (keep# w) (lock s nil)    (lock s' e')
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
evalₛPresId {Δ = Δ #}    (lock s' e)
  = cong₂ lock (evalₛPresId s') refl
