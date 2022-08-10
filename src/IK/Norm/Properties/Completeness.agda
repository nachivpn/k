{-# OPTIONS --without-K #-}
module IK.Norm.Properties.Completeness where


--
-- This module proves the soundness of evaluation (eval-sound),
-- from which the completeness of normalization (norm-complete) follows.
--

open import Data.Unit
  using (⊤ ; tt)
open import Data.Product
  using (Σ ; _×_ ; _,_ ; ∃)

open import Relation.Binary.PropositionalEquality

open import IK.Norm.Base

open import IK.Norm.NbE.Model
open import IK.Norm.NbE.Reification

open import IK.Term

-- soundness relation on semantic values
_≋_ : Tm' Γ a → Tm' Γ a → Set
_≋_ {Γ} {a = ι}      n       m
  = n ≡ m
_≋_ {Γ} {a = a ⇒ b}  f       g
  = {Γ' : Ctx} (w : Γ ⊆ Γ') → {x y : Tm' Γ' a}
    → Psh x → Psh y
    → x ≋ y → f w x ≋ g w y
_≋_ {Γ} {a = □ a}    b       c
  = let box' x = b ; box' y = c in x ≋ y

-- soundness relation on semantic substitutions
data _≋ₛ_ : Sub' Γ Δ → Sub' Γ Δ → Set where
  []   : _≋ₛ_ {Γ = Γ} {Δ = []} tt tt
  _`,_ : {s : Sub' Γ Δ} {s' : Sub' Γ Δ} {x : Tm' Γ a} {y : Tm' Γ a}
       → s ≋ₛ s' → x ≋ y → (s , x) ≋ₛ (s' , y)
  lock : {s : Sub' Γ Δ} {s' : Sub' Γ Δ}
       → s ≋ₛ s' → (e : LFExt Γ' (Γ #) (ΓR))
       → _≋ₛ_ {Γ = Γ'} {Δ = Δ #} (lock s e)  (lock s' e)

------------------------
-- Properties of ≋ and ≋ₛ
------------------------

-- ≋ is symmetric
sym-≋ : {x y : Tm' Γ a}
      → x ≋ y → y ≋ x
sym-≋ {a = ι}     n≡m
  = sym n≡m
sym-≋ {a = a ⇒ b} f≋g
  = λ w px' py' x'≋y' → sym-≋ {a = b} (f≋g w py' px' (sym-≋ {a = a} x'≋y'))
sym-≋ {a = □ a}   b≋c
  = sym-≋ {a = a} b≋c

-- ≋ is transitive
trans-≋ : {x y z : Tm' Γ a}
  → x ≋ y → y ≋ z → x ≋ z
trans-≋ {a = ι}                 n≡m m≡o
  = trans n≡m m≡o
trans-≋ {a = a ⇒ b} {f} {g} {h} f≋g g≋h w {x = x} {y = y} px py x≋y
  = trans-≋ {a = b}
      (f≋g w px py x≋y)
      (g≋h w py py ((trans-≋ {a = a} (sym-≋ {a = a} x≋y) x≋y)))
trans-≋ {a = □ a}               b≋c c≋d
  = trans-≋ {a = a} b≋c c≋d

-- WTH should this thing be called?
pseudo-refl-≋ : {x y : Tm' Γ a}
  → x ≋ y → x ≋ x
pseudo-refl-≋ {a = a} x≋y = trans-≋ {a = a} x≋y (sym-≋ {a = a} x≋y)

-- ≋ₛ is symmetric
sym-≋ₛ : {s s' : Sub' Γ Δ}
      → s ≋ₛ s' → s' ≋ₛ s
sym-≋ₛ {Δ = []}     s≋s'
  = s≋s'
sym-≋ₛ {Δ = Δ `, a} (s≋s' `, x≋y)
  = sym-≋ₛ s≋s' `, sym-≋ {a = a} x≋y
sym-≋ₛ {Δ = Δ #} (lock s≋s' e)
  = lock (sym-≋ₛ s≋s') e

-- ≋ₛ is transitive
trans-≋ₛ : {s s' s'' : Sub' Γ Δ}
    → s ≋ₛ s' → s' ≋ₛ s'' → s ≋ₛ s''
trans-≋ₛ {Δ = []}     s≋s'           s'≋s''
  = []
trans-≋ₛ {Δ = Δ `, a} (s≋s' `, x≋x') (s'≋s'' `, x'≋x'')
  = trans-≋ₛ s≋s' s'≋s'' `, trans-≋ {a = a} x≋x' x'≋x''
trans-≋ₛ {Δ = Δ #}    (lock s≋s' e)  (lock s'≋s'' e)
  = lock (trans-≋ₛ s≋s' s'≋s'') e

-- WTH should this thing be called?
pseudo-refl-≋ₛ : {s s' : Sub' Γ Δ}
  → s ≋ₛ s' → s ≋ₛ s
pseudo-refl-≋ₛ x≋y = trans-≋ₛ x≋y (sym-≋ₛ x≋y)

-- wkTm' preserves the relation _≋_
wkTm'Pres≋ : {x : Tm' Γ a} {y : Tm' Γ a}
  → (w : Γ ⊆ Δ)
  → x ≋ y
  → wkTm' w x ≋ wkTm' w y
wkTm'Pres≋ {a = ι}                     w n≡m
  = cong (wkNf w) n≡m
wkTm'Pres≋ {a = a ⇒ b} {x = f} {y = g} w f≋g
  = λ w' px py x≋y → f≋g (w ∙ w') px py x≋y
wkTm'Pres≋ {a = □ a}                   w b≋c
  = wkTm'Pres≋ {a = a} (keep# w) b≋c

-- wkSub' preserves the relation _≋_
wkSub'Pres≋ : {s s' : Sub' Γ Δ}
  → (w : Γ ⊆ Γ')
  → s ≋ₛ s'
  → wkSub' w s ≋ₛ wkSub' w s'
wkSub'Pres≋ w []
  = []
wkSub'Pres≋ {Δ = Δ `, a} w (s≋s' `, x)
  = wkSub'Pres≋ w s≋s' `, wkTm'Pres≋ {a = a} w x
wkSub'Pres≋ w (lock s≋s e)
  = lock (wkSub'Pres≋ (sliceLeft e w) s≋s) (wkLFExt e w)

--------------------------------------
-- The Fundamental theorem of ≋ and ≋ₛ
--------------------------------------

private

  substVar'Pres≋ : (x : Var Γ a) {s s' : Sub' Δ Γ}
    → s ≋ₛ s'
    → substVar' x s ≋ substVar' x s'
  substVar'Pres≋ zero     {s = _ , x} {s' = _ , y}  (_ `, x≋y)
    = x≋y
  substVar'Pres≋ (succ x) {s = s , _} {s' = s' , _} (s≋s' `, _)
    = substVar'Pres≋ x s≋s'

  unbox'Pres≋ : {b c : Box (Tm'- a) Γ}
    → (e : LFExt Γ' (Γ #) ΓR)
    → b ≋ c
    → unbox' b e ≋ unbox' c e
  unbox'Pres≋ {a = a} e b≋c
    = wkTm'Pres≋ {a = a} (LFExtToWk e) b≋c

--
fund :  (t : Tm Γ a) {s s' : Sub' Δ Γ}
  → Pshₛ s → Pshₛ s'
  → s ≋ₛ s' → eval t s ≋ eval t s'
fund (var x) ps ps' s≋s'
  = substVar'Pres≋ x s≋s'
fund (lam t) {s = s} {s' = s'} ps ps' s≋s' w px py x≋y
  = fund t
      (wkSub'PresPsh w s ps , px)
      (wkSub'PresPsh w s' ps' , py)
      (wkSub'Pres≋ w s≋s' `, x≋y)
fund (app t u) {s = s} {s' = s'} ps ps' s≋s'
  = fund t ps ps' s≋s' idWk (psh-eval u s ps) (psh-eval u s' ps') (fund u ps ps' s≋s')
fund (box t) ps ps' s≋s'
  = fund t ps ps' (lock s≋s' nil)
fund (unbox t nil) {s = lock s e} {s' = lock s' .e} ps ps' (lock s≋s' .e)
  = unbox'Pres≋ {b = eval t s} e (fund t ps ps' s≋s')
fund (unbox t (ext e)) (ps , _) (ps' , _) (s≋s' `, _)
  = fund (unbox t e) ps ps' s≋s'

--
fundₛ :  (s₀ : Sub Γ Δ) {s s' : Sub' Δ' Γ}
  → Pshₛ s → Pshₛ s'
  → s ≋ₛ s' → evalₛ s₀ s ≋ₛ evalₛ s₀ s'
fundₛ []          ps ps' s≋s'
  = []
fundₛ (s₀ `, t)   ps ps' s≋s'
  = (fundₛ s₀ ps ps' s≋s') `, fund t ps ps' s≋s'
fundₛ (lock s₀ (ext e)) {s = s , _} {s' = s' , _} (ps , _) (ps' , _) (s≋s' `, _)
  = fundₛ (lock s₀ e) ps ps' s≋s'
fundₛ (lock s₀ nil) {s = lock s e} {s' = lock s' e} ps ps' (lock s≋s' e)
  = lock (fundₛ s₀ ps ps' s≋s') e

--------------------------
-- Soundness of evaluation
--------------------------

coh-substVar-evalₛ : (x : Var Γ a) (s₀ : Sub Δ Γ) {s s' : Sub' Δ' Δ}
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → substVar' x (evalₛ s₀ s') ≋ eval (substVar s₀ x) s'
coh-substVar-evalₛ zero     (_ `, t) {s} {s'} ps ps' s≋s'
  = pseudo-refl-≋ {x = eval t s'} (sym-≋ {x = eval t s} (fund t ps ps' s≋s'))
coh-substVar-evalₛ (succ x) (s₀ `, _) ps ps' s≋s'
  = coh-substVar-evalₛ x s₀ ps ps' s≋s'

coh-substTm-evalₛ : (t : Tm Γ a) (s₀ : Sub Δ Γ) {s s' : Sub' Δ' Δ}
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t (evalₛ s₀ s') ≋ eval (substTm s₀ t) s'
coh-substTm-evalₛ (var x)     s₀ ps ps' s≋s'
  = coh-substVar-evalₛ x s₀ ps ps' s≋s'
coh-substTm-evalₛ (lam t)     s₀ {s} {s'} ps ps' s≋s' w {x = x} {y} px py x≋y
  rewrite sym (nat-evalₛ w s₀ s' ps')
  = trans-≋ {z =  eval (substTm (wkSub fresh s₀ `, var zero) t) (wkSub' w s' , y)}
      ((subst (λ z → _ ≋ eval t (z , y))
        (trans
          (cong (evalₛ s₀) (sym (trimSub'PresId _)))
          (sym (coh-trimSub'-wkSub fresh s₀ (wkSub' w s' , y))))
        (fund t
          (psh-evalₛ s₀ _ (wkSub'PresPsh w s' ps') , px)
          (psh-evalₛ s₀ _ (wkSub'PresPsh w s' ps') , py)
          (fundₛ s₀
            (wkSub'PresPsh w s' ps')
            (wkSub'PresPsh w s' ps')
            (wkSub'Pres≋ w ((pseudo-refl-≋ₛ {s = s'} (sym-≋ₛ s≋s')))) `, x≋y))))
      ((coh-substTm-evalₛ t
        (keepₛ s₀)
        (wkSub'PresPsh w s ps , px)
        (wkSub'PresPsh w s' ps' , py)
        (wkSub'Pres≋ w s≋s' `, x≋y)))
coh-substTm-evalₛ (app t u)  s₀ ps ps' s≋s'
  = coh-substTm-evalₛ t s₀ ps ps' s≋s' idWk
      (psh-eval u _ (psh-evalₛ s₀ _ ps'))
      (psh-eval (substTm s₀ u) _ ps')
      (coh-substTm-evalₛ u s₀ ps ps' s≋s')
coh-substTm-evalₛ (box t)     s₀ ps ps' s≋s'
  = coh-substTm-evalₛ t (lock s₀ nil) ps ps' (lock s≋s' nil)
coh-substTm-evalₛ (unbox t (ext e)) (s₀ `, _) ps ps' s≋s'
  = coh-substTm-evalₛ (unbox t e) s₀ ps ps' s≋s'
coh-substTm-evalₛ (unbox t nil) (lock s₀ (ext e)) (ps , _) (ps' , _) (s≋s' `, _)
  = coh-substTm-evalₛ (unbox t nil) (lock s₀ e) ps ps' s≋s'
coh-substTm-evalₛ (unbox t nil) (lock s₀ nil) {s = lock s e} {s' = lock s' e'} ps ps' (lock s≋s' e')
  = unbox'Pres≋ {b = eval t (evalₛ s₀ s')} e' (coh-substTm-evalₛ t s₀ ps ps' s≋s')

private
  lemma1 : {t : Tm (ΓL #) a} (e : LFExt Γ (ΓL #) ΓR) {s s' : Sub' Δ Γ}
    → Pshₛ s → Pshₛ s'
    → s ≋ₛ s'
    → eval (unbox (box t) e) s ≋ eval t (trimSub' (LFExtToWk e) s')
  lemma1 {t = t} nil {s = lock s e} {s' = lock s' e} ps ps' (lock s≋s' e)
    with ←#IsPre# e | #→IsPost# e
  ... | refl | refl
    rewrite sym (nat-eval t (LFExtToWk e) (lock s nil) ps)
      | ExtIsProp (wkLFExt nil (LFExtToWk e)) e
        = fund t
               (wkSub'PresPsh (sliceLeft nil (LFExtToWk e)) s ps)
               (subst Pshₛ (sym (trimSub'PresId s')) ps')
               (lock lemma1-2 e)
    where
      lemma1-1' : ∀ (e : LFExt Γ ΓL ΓR) → (p : ΓL ≡ ←# Γ #) → sliceLeft nil (LFExtToWk (subst (λ ΓL → LFExt Γ ΓL ΓR) p e)) ≡ idWk
      lemma1-1' {Γ = Γ #}    nil     p    rewrite Ctx-K p = refl
      lemma1-1' {Γ = Γ `, a} (ext e) refl                 = lemma1-1' e refl
      lemma1-1 : ∀ (e : LFExt Γ (←# Γ #) ΓR) → sliceLeft nil (LFExtToWk e) ≡ idWk
      lemma1-1 e = lemma1-1' e refl
      lemma1-2 : wkSub' (sliceLeft nil (LFExtToWk e)) s ≋ₛ trimSub' idWk s'
      lemma1-2 rewrite lemma1-1 e
        | trimSub'PresId s'
        | wkSub'PresId s = s≋s'
  lemma1 {t = t} (ext e) (s  , _) (s' , _) (s≋s' `, _)
    = lemma1 {t = t} e s s' s≋s'

  lemma2 : {b c : Tm' Γ (□ a)}
    → b ≋ c
    → b ≋ box' (unbox' c new)
  lemma2 {c = c} b≋c rewrite (let box' y = c in wkTm'PresId y)
      = b≋c

-- soundness of evaluation wrt single-step reduction
eval-sound-red : {t t' : Tm Γ a} {s s' : Sub' Δ Γ}
  → t ⟶ t'
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t s ≋ eval t' s'
eval-sound-red {Γ = Γ} {Δ = Δ} {t = app (lam {b = b} t) u} {s = s} {s' = s'} red-fun ps ps' s≋s'
  rewrite wkSub'PresId s
  | evalₛPresId s'
    = trans-≋ {Γ = Δ} {a = b}
      (fund t
            (ps , (psh-eval u s ps))
            (subst Pshₛ (sym (evalₛPresId s')) ps' , psh-eval u s' ps')
            (subst (s ≋ₛ_) (sym (evalₛPresId s')) s≋s' `, fund u ps ps' s≋s'))
      (coh-substTm-evalₛ t (idₛ `, u) {s} {s'} ps ps' s≋s')
eval-sound-red {t = t} {s = s} {s'} exp-fun  ps ps' s≋s' w {x = x} px py x≋y
  rewrite sym (rightIdWk w)
  | sym (cong (λ f → f idWk x) (nat-eval t w s ps))
  | sym (trimSub'PresId (wkSub' w s))
  | rightIdWk w
  | sym (coh-trimSub'-wkTm fresh (wkSub' w s , x) t)
    = fund (wkTm (drop idWk) t)
           (wkSub'PresPsh w s ps , px)
           (wkSub'PresPsh w s' ps' , py)
           (wkSub'Pres≋ w s≋s' `, x≋y)
           idWk
           px
           py
           x≋y
eval-sound-red {t = unbox (box t) e} {s = s} {s' = s'} red-box ps ps' s≋s'
  rewrite coh-trimSub'-wkTm (LFExtToWk e) s' t
  = lemma1 {t = t} e ps ps' s≋s'
eval-sound-red {t = t} {s = s} {s'} exp-box ps ps' s≋s'
  = lemma2 {b = eval t s} (fund t ps ps' s≋s')
eval-sound-red {t = t} {s = s} {s'} (cong-lam r) ps ps' s≋s' w {x = x} px py x≋y
  = eval-sound-red r
      (wkSub'PresPsh w s ps , px)
      (wkSub'PresPsh w s' ps' , py)
      ((wkSub'Pres≋ w s≋s') `, x≋y)
eval-sound-red {t = app t u} {t' = app t' u'} {s = s} {s' = s'} (cong-app1 r) ps ps' s≋s'
  = eval-sound-red r ps ps' s≋s'
      idWk
      (psh-eval u s ps)
      (psh-eval u s' ps')
      (fund u ps ps' s≋s')
eval-sound-red {t = app t u} {t' = app t' u'} {s = s} {s' = s'} (cong-app2 r) ps ps' s≋s'
  = fund t ps ps' s≋s' idWk (psh-eval u s ps) (psh-eval u' s' ps') (eval-sound-red r ps ps' s≋s')
eval-sound-red (cong-box r) ps ps' s≋s'
  = eval-sound-red r ps ps' (lock s≋s' nil)
eval-sound-red {s = lock s e} {s' = lock s' .e} (cong-unbox {t = t} {e = nil} r) ps ps' (lock s≋s' e)
  = unbox'Pres≋ {b = eval t s} e (eval-sound-red r ps ps' s≋s')
eval-sound-red {s = s , _} {s' = s' , _} (cong-unbox {t = t} {e = ext e} r) (ps , _) (ps' , _) (s≋s' `, _)
  = eval-sound-red (cong-unbox {e = e} r) ps ps' s≋s'

-- soundness of evaluation wrt multi-step reduction
eval-sound-red* : {t t' : Tm Γ a} {s s' : Sub' Δ Γ}
  → t ⟶* t'
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t s ≋ eval t' s'
eval-sound-red* {t = t} {t' = .t} ε        ps ps' s≋s'
  = fund t ps ps' s≋s'
eval-sound-red* {a = a} {t = t} {t' = t'} (r ◅ rs) ps ps' s≋s'
  = trans-≋ {a = a} (eval-sound-red r ps ps' s≋s') (eval-sound-red* rs ps' ps' (pseudo-refl-≋ₛ (sym-≋ₛ s≋s')))

-- soundness of evaluation wrt conversion
eval-sound : {t t' : Tm Γ a} {s s' : Sub' Δ Γ}
  → t ≈ t'
  → Pshₛ s → Pshₛ s' → s ≋ₛ s' → eval t s ≋ eval t' s'
eval-sound {t = t} ε ps ps' s≋s'
  = eval-sound-red* {t = t} ⟶*-refl ps ps' s≋s'
eval-sound {a = a} (inj₁ r ◅ t≈t') ps ps' s≋s'
  = trans-≋ {a = a} (eval-sound-red r ps ps' s≋s') (eval-sound t≈t' ps' ps' (pseudo-refl-≋ₛ (sym-≋ₛ s≋s')))
eval-sound {a = a} {t = t} {s = s} {s' = s'} (inj₂ r ◅ t≈t') ps ps' s≋s'
  = trans-≋ {a = a}
      (sym-≋ {y = eval t s} (eval-sound-red r ps' ps (sym-≋ₛ s≋s')))
      (eval-sound t≈t' ps' ps' (pseudo-refl-≋ₛ (sym-≋ₛ s≋s')))

--------------------------------------------------------
-- Uniqueness of reification and soundness of reflection
--------------------------------------------------------

unique-reify : {x y : Tm' Γ a}
  → x ≋ y → reify x ≡ reify y
sound-reflect : {n n' : Ne Γ a}
  → n ≡ n' → reflect n ≋ reflect n'

unique-reify {a = ι}     n≡m = n≡m
unique-reify {a = a ⇒ b} f≋g = cong lam
  (unique-reify
    (f≋g fresh (psh-reflect {a = a} (var zero)) (psh-reflect {a = a} (var zero))
    (sound-reflect {a = a} refl)))
unique-reify {a = □ a}   b≋c
  = cong box (unique-reify b≋c)

sound-reflect {a = ι}      n≡n'
  = cong up n≡n'
sound-reflect {a = a ⇒ b}  n≡n' w px py x≋y
  = sound-reflect {a = b} (cong₂ app (cong (wkNe w) n≡n') (unique-reify x≋y))
sound-reflect {a = □ a}    n≡n'
  = sound-reflect {a = a} (cong₂ unbox n≡n' refl)

--------------------------------
-- Completeness of normalization
--------------------------------

idₛ'≋idₛ' : {Γ : Ctx} → idₛ' {Γ} ≋ₛ idₛ'
idₛ'≋idₛ' {[]}     = []
idₛ'≋idₛ' {Γ `, a} = (wkSub'Pres≋ fresh (idₛ'≋idₛ' {Γ})) `, (sound-reflect {a = a} refl)
idₛ'≋idₛ' {Γ #}    = lock idₛ'≋idₛ' nil

norm-complete-red* : {t t' : Tm Γ a} → t ⟶* t' → norm t ≡ norm t'
norm-complete-red* {Γ = Γ} r = unique-reify (eval-sound-red* r (psh-idₛ' {Γ}) (psh-idₛ' {Γ}) idₛ'≋idₛ')

norm-complete : {t t' : Tm Γ a} → t ≈ t' → norm t ≡ norm t'
norm-complete {Γ = Γ} p = unique-reify (eval-sound p (psh-idₛ' {Γ}) (psh-idₛ' {Γ}) idₛ'≋idₛ')
