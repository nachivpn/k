module IS4.HellOfSyntacticLemmas where

-- Welcome to the hell of mind-numbing syntactic lemmas.
-- No good ever comes from proving these lemmas, but no
-- good can happen without proving them.

open import Data.Product  using (Σ ; _×_ ; _,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Product.Properties using (Σ-≡,≡↔≡; ×-≡,≡↔≡)

open import Function using (Inverse)

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ; ≅-to-≡ ; ≡-subst-removable)

open import IS4.Term
open import IS4.Norm

open ≡-Reasoning

-- HE utilities
module _ where

  open import Level           using (Level)
  open import Relation.Unary  using (Pred)
  open import Relation.Binary using (REL)

  infixr 2 step-≅

  private
    variable
      ℓ : Level
      A : Set ℓ
      B : Set ℓ

  ≡-subst-addable : ∀ (P : Pred A ℓ) {x y} (eq : x ≡ y) (z : P x) → z ≅ subst P eq z
  ≡-subst-addable P p z = HE.sym (≡-subst-removable P p z)

  -- stole it from history of master
  ≡-subst₂-removable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → subst₂ R eq₁ eq₂ z ≅ z
  ≡-subst₂-removable P refl refl z = HE.refl

  ≡-subst₂-addable : ∀ (R : REL A B ℓ) {x y u v} (eq₁ : x ≡ y) (eq₂ : u ≡ v) (z : R x u) → z ≅ subst₂ R eq₁ eq₂ z
  ≡-subst₂-addable P p q z = HE.sym (≡-subst₂-removable P p q z)

  step-≅ : ∀ (x {y z} : A) → y ≡ z → x ≅ y → x ≡ z
  step-≅ _ y≡z x≅y = trans (≅-to-≡ x≅y) y≡z

  syntax step-≅ x y≡z x≡y = x ≅⟨ x≡y ⟩ y≡z

module _
  (T : Ctx → Set)                             -- Type of indexed sets (terms, etc.)
  (E : Ctx → Ctx → Set)                       -- Type of context extensions
  {R : {ΓL ΓR : Ctx} → T ΓL → E ΓL ΓR → Set}  -- ... (unbox, lock, etc.)
  where

  -- Custom combinator to prove syntactic lemmas about unbox, lock, etc.
  xcong : {i1 i2 j1 j2 : Ctx} →
           i1 ≡ i2 → j1 ≡ j2 →
          {t1 : T i1} {t2 : T i2} {e1 : E i1 j1} {e2 : E i2 j2}
          (unb : {i j : Ctx} → (t : T i ) (e : E i j) → R t e) →
          t1 ≅ t2 →
          e1 ≅ e2 →
          unb t1 e1 ≅ unb t2 e2
  xcong refl refl _ HE.refl HE.refl = HE.refl

wkTmPresId : (t : Tm Γ a) → wkTm idWk t ≡ t
wkTmPresId (var x)     = cong var (wkVarPresId x)
wkTmPresId (lam t)     = cong lam (wkTmPresId t)
wkTmPresId (app t u)   = cong₂ app (wkTmPresId t) (wkTmPresId u)
wkTmPresId (box t)     = cong box (wkTmPresId t)
wkTmPresId {Γ = Γ} {a = a} (unbox {ΓL = ΓL} {ΓR = ΓR} t e) = begin
  wkTm idWk (unbox t e)
    ≡⟨⟩
  unbox {ΓL = f2LCtx e idWk} {ΓR = f2RCtx e idWk} (wkTm (factor2≤ e idWk[ Γ ]) t) (factor2Ext e idWk[ Γ ])
    ≅⟨ xcong
      (λ ΓL → Tm ΓL (◻ a)) (CExt Γ)
      (f2LCtxPresId e) (f2RCtxPresId e)
      unbox
      factor2≤PresId-under-wkTm
      (≡-subst₂-addable (CExt Γ) _ _ (factor2Ext _ _)) ⟩
  unbox {ΓL = ΓL} {ΓR = ΓR} (wkTm idWk[ ΓL ] t) (subst₂ (CExt Γ) (f2LCtxPresId e) (f2RCtxPresId e) (factor2Ext e idWk))
    ≡⟨ cong₂ unbox (wkTmPresId t) (factor2ExtPresId e) ⟩
  unbox t e ∎
    where
      factor2≤PresId-under-wkTm : wkTm (factor2≤ e idWk) t ≅ wkTm idWk t
      factor2≤PresId-under-wkTm = HE.icong (ΓL ⊆_) (f2LCtxPresId e) (λ w → wkTm w t)
        (HE.trans (≡-subst-addable _ _ _) (HE.≡-to-≅ (factor2≤PresId e)))

wkSubPresId : (s : Sub Δ Γ) → wkSub idWk s ≡ s
wkSubPresId []         = refl
wkSubPresId (s `, t)   = cong₂ _`,_ (wkSubPresId s) (wkTmPresId t)
wkSubPresId {Δ = Δ} (lock {ΔL = ΔL} {Γ = Γ} s e) = begin
  wkSub idWk (lock s e)
    ≡⟨⟩
  lock (wkSub (factor2≤ e idWk) s) (factor2Ext e idWk)
    ≅⟨ xcong
      (λ ΔL → Sub ΔL Γ) (CExt Δ)
      (f2LCtxPresId e) (f2RCtxPresId e)
      lock
      factor2≤PresId-under-wkSub
      (≡-subst₂-addable (CExt Δ) _ _ (factor2Ext _ _)) ⟩
  lock (wkSub idWk s) (subst₂ (CExt Δ) (f2LCtxPresId e) (f2RCtxPresId e) (factor2Ext e idWk))
    ≡⟨ cong₂ lock (wkSubPresId s) (factor2ExtPresId e) ⟩
  lock s e ∎
    where
      factor2≤PresId-under-wkSub : wkSub (factor2≤ e idWk) s ≅ wkSub idWk s
      factor2≤PresId-under-wkSub = HE.icong (ΔL ⊆_) (f2LCtxPresId e) (λ w → wkSub w s)
        (HE.trans (≡-subst-addable _ _ _) (HE.≡-to-≅ (factor2≤PresId e)))

wkNePresId : (n : Ne Γ a) → wkNe idWk n ≡ n
wkNfPresId : (n : Nf Γ a) → wkNf idWk n ≡ n

wkNePresId (var x)     = cong var (wkVarPresId x)
wkNePresId (app n m)   = cong₂ app (wkNePresId n) (wkNfPresId m)
wkNePresId {Γ = Γ} (unbox {ΓL = ΓL} {a = a} n e) = begin
  wkNe idWk (unbox n e)
    ≡⟨⟩
  unbox (wkNe (factor2≤ e idWk) n) (factor2Ext e idWk)
    ≅⟨ xcong
      (λ ΓL → Ne ΓL (◻ a)) (CExt Γ)
      (f2LCtxPresId e) (f2RCtxPresId e)
      unbox
      factor2≤PresId-under-wkNe
      (≡-subst₂-addable (CExt Γ) _ _ (factor2Ext _ _)) ⟩
  unbox (wkNe idWk n) (subst₂ (CExt Γ) (f2LCtxPresId e) (f2RCtxPresId e) (factor2Ext e idWk))
    ≡⟨ cong₂ unbox (wkNePresId n) (factor2ExtPresId e) ⟩
  unbox n e ∎
    where
      factor2≤PresId-under-wkNe : wkNe (factor2≤ e idWk) n ≅ wkNe idWk n
      factor2≤PresId-under-wkNe = HE.icong (ΓL ⊆_) (f2LCtxPresId e) (λ w → wkNe w n)
        (HE.trans (≡-subst-addable _ _ _) (HE.≡-to-≅ (factor2≤PresId e)))

wkNfPresId (up𝕓 n) = cong up𝕓 (wkNePresId n)
wkNfPresId (lam n) = cong lam (wkNfPresId n)
wkNfPresId (box n) = cong box (wkNfPresId n)

wkTmPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (t : Tm Γ a)
  → wkTm w' (wkTm w t) ≡ wkTm (w ∙ w') t
wkTmPres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkTmPres∙ w w' (lam t)     = cong lam (wkTmPres∙ (keep w) (keep w') t)
wkTmPres∙ w w' (app t u)   = cong₂ app (wkTmPres∙ w w' t) (wkTmPres∙ w w' u)
wkTmPres∙ w w' (box t)     = cong box (wkTmPres∙ (keep🔒 w) (keep🔒 w') t)
wkTmPres∙ {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} w w' (unbox {ΓL = ΓL} {a = a} {ΓR = ΓR} t e) = begin
  wkTm w' (wkTm w (unbox t e))
    ≡⟨⟩
  unbox {ΓL = f2LCtx (factor2Ext e w) w'} {ΓR = f2RCtx (factor2Ext e w) w'}
    (wkTm (factor2≤ (factor2Ext e w) w') (wkTm (factor2≤ e w) t))
    (factor2Ext (factor2Ext e w) w')
    ≡⟨ cong₂ unbox (wkTmPres∙ _ _ t) (sym (factor2ExtPres∙ _ _ _)) ⟩
  unbox {ΓL = f2LCtx (factor2Ext e w) w'} {ΓR = f2RCtx (factor2Ext e w) w'}
    (wkTm (factor2≤ e w ∙ factor2≤ (factor2Ext e w) w') t)
    (subst₂ (CExt Γ'') (f2LCtxPres∙ e w w') (f2RCtxPres∙ e w w') (factor2Ext e (w ∙ w')))
    ≅⟨ xcong
      (λ ΓL → Tm ΓL (◻ a)) (CExt Γ'')
      (sym (f2LCtxPres∙ e w w')) (sym (f2RCtxPres∙ e w w'))
      unbox
      factor2≤Pres∙-under-wkTm
      (≡-subst₂-removable (CExt Γ'') (f2LCtxPres∙ e w w') (f2RCtxPres∙ e w w') (factor2Ext e (w ∙ w'))) ⟩
  unbox {ΓL = f2LCtx e (w ∙ w')} {ΓR = f2RCtx e (w ∙ w')} (wkTm (factor2≤ e (w ∙ w')) t) (factor2Ext e (w ∙ w'))
    ≡⟨⟩
  wkTm (w ∙ w') (unbox t e) ∎
    where
      factor2≤Pres∙-under-wkTm :  wkTm (factor2≤ e w ∙ factor2≤ (factor2Ext e w) w') t ≅ wkTm (factor2≤ e (w ∙ w')) t
      factor2≤Pres∙-under-wkTm = HE.icong (ΓL ⊆_) (sym (f2LCtxPres∙ e w w')) (λ w → wkTm w t)
        (HE.trans (HE.≡-to-≅ (sym (factor2≤Pres∙ e w w'))) (≡-subst-removable _ _ _))

wkSubPres∙ : (w : Δ ⊆ Δ') (w' : Δ' ⊆ Δ'') (s : Sub Δ Γ)
  → wkSub w' (wkSub w s) ≡ wkSub (w ∙ w') s
wkSubPres∙ w w' []         = refl
wkSubPres∙ w w' (s `, t)   = cong₂ _`,_ (wkSubPres∙ w w' s) (wkTmPres∙ w w' t)
wkSubPres∙ {Δ'' = Δ''} w w' (lock {ΔL = ΔL} {Γ = Γ} s e) = begin
  wkSub w' (wkSub w (lock s e))
    ≡⟨⟩
  lock (wkSub (factor2≤ (factor2Ext e w) w') (wkSub (factor2≤ e w) s)) (factor2Ext (factor2Ext e w) w')
    ≡⟨ cong₂ lock (wkSubPres∙ _ _ _ ) (sym (factor2ExtPres∙ _ _ _)) ⟩
  lock
    (wkSub (factor2≤ e w ∙ factor2≤ (factor2Ext e w) w') s)
    (subst₂ (CExt Δ'') (f2LCtxPres∙ e w w') (f2RCtxPres∙ e w w') (factor2Ext e (w ∙ w')))
    ≅⟨ xcong
      (λ ΔL → Sub ΔL Γ) (CExt Δ'')
      (sym (f2LCtxPres∙ e w w')) (sym (f2RCtxPres∙ e w w'))
      lock
      factor2≤Pres∙-under-wkSub
      (≡-subst₂-removable (CExt Δ'') (f2LCtxPres∙ e w w') (f2RCtxPres∙ e w w') (factor2Ext e (w ∙ w'))) ⟩
  lock (wkSub (factor2≤ e (w ∙ w')) s) (factor2Ext e (w ∙ w'))
    ≡⟨⟩
  wkSub (w ∙ w') (lock s e) ∎
    where
      factor2≤Pres∙-under-wkSub :  wkSub (factor2≤ e w ∙ factor2≤ (factor2Ext e w) w') s ≅ wkSub (factor2≤ e (w ∙ w')) s
      factor2≤Pres∙-under-wkSub = HE.icong (ΔL ⊆_) (sym (f2LCtxPres∙ e w w')) (λ w → wkSub w s)
        (HE.trans (HE.≡-to-≅ (sym (factor2≤Pres∙ e w w'))) (≡-subst-removable _ _ _))

wkNePres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Ne Γ a)
  → wkNe w' (wkNe w n) ≡ wkNe (w ∙ w') n
wkNfPres∙ : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'') (n : Nf Γ a)
  → wkNf w' (wkNf w n) ≡ wkNf (w ∙ w') n

wkNePres∙ w w' (var x)     = cong var (wkVarPres∙ w w' x)
wkNePres∙ w w' (app n m)   = cong₂ app (wkNePres∙ w w' n) (wkNfPres∙ w w' m)
wkNePres∙ {Γ'' = Γ''} w w' (unbox {ΓL = ΓL} {a = a} n e) = begin
  wkNe w' (wkNe w (unbox n e))
    ≡⟨⟩
  unbox
    (wkNe (factor2≤ (factor2Ext e w) w') (wkNe (factor2≤ e w) n))
    (factor2Ext (factor2Ext e w) w')
    ≡⟨ cong₂ unbox (wkNePres∙ _ _ n) (sym (factor2ExtPres∙ _ _ _)) ⟩
  unbox
    (wkNe (factor2≤ e w ∙ factor2≤ (factor2Ext e w) w') n)
    (subst₂ (CExt Γ'') (f2LCtxPres∙ e w w') (f2RCtxPres∙ e w w') (factor2Ext e (w ∙ w')))
    ≅⟨ xcong
      (λ ΓL → Ne ΓL (◻ a)) (CExt Γ'')
      (sym (f2LCtxPres∙ e w w')) (sym (f2RCtxPres∙ e w w'))
      unbox
      factor2≤Pres∙-under-wkNe
      (≡-subst₂-removable (CExt Γ'') (f2LCtxPres∙ e w w') (f2RCtxPres∙ e w w') (factor2Ext e (w ∙ w'))) ⟩
  unbox {ΓL = f2LCtx e (w ∙ w')} {ΓR = f2RCtx e (w ∙ w')} (wkNe (factor2≤ e (w ∙ w')) n) (factor2Ext e (w ∙ w'))
    ≡⟨⟩
  wkNe (w ∙ w') (unbox n e) ∎
    where
      factor2≤Pres∙-under-wkNe :  wkNe (factor2≤ e w ∙ factor2≤ (factor2Ext e w) w') n ≅ wkNe (factor2≤ e (w ∙ w')) n
      factor2≤Pres∙-under-wkNe = HE.icong (ΓL ⊆_) (sym (f2LCtxPres∙ e w w')) (λ w → wkNe w n)
        (HE.trans (HE.≡-to-≅ (sym (factor2≤Pres∙ e w w'))) (≡-subst-removable _ _ _))

wkNfPres∙ w w' (up𝕓 n) = cong up𝕓 (wkNePres∙ w w' n)
wkNfPres∙ w w' (lam n) = cong lam (wkNfPres∙ (keep w) (keep w') n)
wkNfPres∙ w w' (box n) = cong box (wkNfPres∙ (keep🔒 w) (keep🔒 w') n)
