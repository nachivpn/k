module IS4.Conversion where

open import HEUtil
open import IS4.Term
open import IS4.Reduction
  as Reduction
open import IS4.HellOfSyntacticLemmas

import Data.Sum as Sum

open import Relation.Nullary
  using (¬_)

open import Relation.Binary
  using (Setoid)

open import Relation.Binary.Construct.Closure.Equivalence
  using (setoid)
import Relation.Binary.Construct.Closure.Equivalence.Properties
  as EquivalenceProperties

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  as ReflexiveTransitive
  using (Star)

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)

open import Relation.Binary.HeterogeneousEquality as HE
  using (_≅_)
  renaming (refl to ≅-refl ; sym to ≅-sym ; trans to ≅-trans)

open Sum public
  using (inj₁ ; inj₂)
open ReflexiveTransitive public
  using (ε ; _◅_)
open EquivalenceProperties public
  using    ()
  renaming (a—↠b⇒a↔b to ⟶*-to-≈)

-- Convertibility is defined taking the
-- equivalence closure of the reduction relation.
Tm-setoid : (Γ : Ctx) → (a : Ty) → Setoid _ _
Tm-setoid Γ a = setoid (_⟶_ {Γ} {a})

module _ {Γ : Ctx} {a : Ty} where
  open Setoid (Tm-setoid Γ a) public
    using    (_≈_)
    renaming (refl to ≈-refl ; reflexive to ≡-to-≈ ; sym to ≈-sym ; trans to ≈-trans ; isEquivalence to ≈-equiv)

≡˘-to-≈ : t' ≡ t → t ≈ t'
≡˘-to-≈ t'≡t = ≡-to-≈ (≡-sym t'≡t)

⟶-to-≈ : t ⟶ t' → t ≈ t'
⟶-to-≈ p = inj₁ p ◅ ε

⟵-to-≈ : t' ⟶ t → t ≈ t'
⟵-to-≈ p = inj₂ p ◅ ε

module _ {t : Tm Γ a → Tm Δ b} (cong-t : ∀ {u u' : Tm Γ a} → (u⟶u' : u ⟶ u') → t u ⟶ t u') where
  -- XXX: fold
  cong-⟶-to-cong-≈ : ∀ (u≈u' : u ≈ u') → t u ≈ t u'
  cong-⟶-to-cong-≈ ε                     = ε
  cong-⟶-to-cong-≈ (inj₁ u⟶u'' ◅ u''≈u') = inj₁ (cong-t u⟶u'') ◅ cong-⟶-to-cong-≈ u''≈u'
  cong-⟶-to-cong-≈ (inj₂ u⟵u'' ◅ u''≈u') = inj₂ (cong-t u⟵u'') ◅ cong-⟶-to-cong-≈ u''≈u'

red-fun≈ : (t : Tm (Γ `, a) b) (u : Tm Γ a) → (app (lam t) u) ≈ substTm (idₛ `, u) t
red-fun≈ t u = ⟶-to-≈ (Reduction.red-fun t u)

exp-fun≈ : (t : Tm Γ (a ⇒ b)) → t ≈ lam (app (wkTm fresh t) (var ze))
exp-fun≈ t = ⟶-to-≈ (Reduction.exp-fun t)

red-box≈ : (t : Tm (ΓL 🔒) a) (e : CExt Γ ΓL ΓR) → unbox (box t) e ≈ substTm (lock idₛ e) t
red-box≈ t e = ⟶-to-≈ (Reduction.red-box t e)

exp-box≈ : (t : Tm Γ (◻ a)) → t ≈ box (unbox t new)
exp-box≈ t = ⟶-to-≈ (Reduction.exp-box t)

cong-lam≈ : ∀ (t≈t' : t ≈ t') → lam t ≈ lam t'
cong-lam≈ = cong-⟶-to-cong-≈ Reduction.cong-lam

cong-app1≈ : ∀ (t≈t' : t ≈ t') → app t u ≈ app t' u
cong-app1≈ = cong-⟶-to-cong-≈ Reduction.cong-app1

cong-app2≈ : ∀ (u≈u' : u ≈ u') → app t u ≈ app t u'
cong-app2≈ = cong-⟶-to-cong-≈ Reduction.cong-app2

cong-app≈ : ∀ (t≈t' : t ≈ t') (u≈u' : u ≈ u') → app t u ≈ app t' u'
cong-app≈ t≈t' u≈u' = ≈-trans (cong-app1≈ t≈t') (cong-app2≈ u≈u')

cong-box≈ : ∀ (t≈t' : t ≈ t') → box t ≈ box t'
cong-box≈ = cong-⟶-to-cong-≈ Reduction.cong-box

cong-unbox1≈ : ∀ (t≈t' : t ≈ t') → unbox t e ≈ unbox t' e
cong-unbox1≈ = cong-⟶-to-cong-≈ Reduction.cong-unbox

cong-unbox2≈ : ∀ (e≡e' : e ≡ e') → unbox t e ≈ unbox t e'
cong-unbox2≈ e≡e' = ≡-to-≈ (cong₂ unbox ≡-refl e≡e')

cong-unbox≈ : ∀ (t≈t' : t ≈ t') (e≡e' : e ≡ e') → unbox t e ≈ unbox t' e'
cong-unbox≈ t≈t' e≡e' = ≈-trans (cong-unbox1≈ t≈t') (cong-unbox2≈ e≡e')

data _≈ₛ_ : Sub Δ Γ → Sub Δ Γ → Set where
  ≈ₛ-refl    : {s : Sub Δ Γ}
    → s ≈ₛ s
  ≈ₛ-trans   : {s s' s'' : Sub Δ Γ}
    → s ≈ₛ s' → s' ≈ₛ s'' → s ≈ₛ s''
  ≈ₛ-sym     : {s s' : Sub Δ Γ}
    → s ≈ₛ s' → s' ≈ₛ s
  cong-`,≈ₛ   : {s s' : Sub Δ Γ} {t t' : Tm Δ a}
    → s ≈ₛ s' → t ≈ t' → (s `, t) ≈ₛ (s' `, t')
  cong-lock≈ₛ  : {s s' : Sub ΔL ΓL} {e : CExt Δ ΔL ΔR}
    → s ≈ₛ s' → lock s e ≈ₛ lock s' e
  shift-lock≈ₛ : {ΔLL ΔLR : Ctx} {s : Sub ΔLL Γ} {e : LFExt ΔL ΔLL ΔLR} {e' : CExt Δ ΔL ΔR}
    → lock s (extRAssoc (upLFExt e) e') ≈ₛ lock (wkSub (LFExtTo⊆ e) s) e'

≡-to-≈ₛ : {s s' : Sub Δ Γ} → s ≡ s' → s ≈ₛ s'
≡-to-≈ₛ ≡-refl = ≈ₛ-refl

Sub-setoid : (Γ Δ : Ctx) → Setoid _ _
Sub-setoid Γ Δ = record {
  Carrier         = Sub Γ Δ
  ; _≈_           = _≈ₛ_
  ; isEquivalence = record {
    refl    = ≈ₛ-refl
    ; sym   = ≈ₛ-sym
    ; trans = ≈ₛ-trans } }

---------
-- Lemmas
---------

invRed :  {t t' : Tm Γ a}
  → (w : Γ ⊆ Γ')
  → t ⟶ t'
  → wkTm w t ≈ wkTm w t'
invRed w (red-fun t u)
  = ≈-trans (⟶-to-≈ (red-fun _ _)) (≡-to-≈ (beta-wk-lemma w u t))
invRed w (exp-fun _)
  = ≈-trans (⟶-to-≈ (exp-fun _)) (≡-to-≈ (cong lam (cong₂ app keepFreshLemma ≡-refl)))
invRed w (red-box t e)
  = ≈-trans
    (⟶-to-≈ (red-box _ _))
    (≈-trans
      (≈-trans
        (≡-to-≈ (≡-sym (coh-trimSub-wkTm t _ _)))
        (≡-to-≈
          (cong
            (λ s → substTm (lock s (factorExt e w)) t)
            (≡-trans
              (trimSubId (factorWk e w))
              (≡-sym (wkSubId _))))))
      (≡-to-≈ (nat-substTm t _ _)))
invRed w (exp-box _)
  = ⟶-to-≈ (exp-box _)
invRed w (cong-lam r)
  = cong-lam≈ (invRed (keep w) r)
invRed w (cong-box r)
  = cong-box≈ (invRed (keep🔒 w) r)
invRed w (cong-unbox {e = e} r)
  = cong-unbox≈ (invRed (factorWk e w ) r) ≡-refl
invRed w (cong-app1 r)
  = cong-app≈ (invRed w r) ε
invRed w (cong-app2 r)
  = cong-app≈ ε (invRed w r)
invRed {a = a} {Γ' = Γ'} w (shift-unbox t e e')
  = begin
    wkTm w (unbox t (extRAssoc (upLFExt e) e'))
      ≡⟨⟩
    unbox
      (wkTm (factorWk (extRAssoc (upLFExt e) e') w) t)
      (factorExt (extRAssoc (upLFExt e) e') w)
      -- add substs
      ≡⟨ ≅-to-≡ (cong-unbox≅
        (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w)
        (≡-subst-addable _ _ _) (≡-subst₂-addable _ _ _ _)) ⟩
    unbox
      (subst (λ ΓL → Tm ΓL _) (lCtxPresTrans (upLFExt e) e' w) (wkTm (factorWk (extRAssoc (upLFExt e) e') w) t))
      (subst₂ (CExt _) (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w) (factorExt (extRAssoc (upLFExt e) e') w))
      -- push subst on subterm inside
      ≡⟨ cong₂ unbox (subst-application′ (_ ⊆_) (λ w → wkTm w t) (lCtxPresTrans (upLFExt e) e' w)) ≡-refl ⟩
   unbox
      (wkTm (subst (_ ⊆_) (lCtxPresTrans (upLFExt e) e' w) (factorWk (extRAssoc (upLFExt e) e') w)) t)
      (subst₂ (CExt _) (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w) (factorExt (extRAssoc (upLFExt e) e') w))
      -- factorisation preserves transitivity
      ≡⟨ cong₂ unbox (cong₂ wkTm (factorWkPresTrans (upLFExt e) e' w) ≡-refl) (factorExtPresTrans (upLFExt e) _ _) ⟩
    unbox
      (wkTm (factorWk (upLFExt e) (factorWk e' w)) t)
      (extRAssoc (factorExt (upLFExt e) (factorWk e' w)) (factorExt e' w))
      -- apply equalities for absorption of upLFExt
      ≡⟨ cong₂ unbox (cong₂ wkTm (≡-sym (factorWkAbsorbsUpLFExt e (factorWk e' w))) ≡-refl) (cong₂ extRAssoc (≡-sym (factorExtAbsorbsUpLFExt e (factorWk e' w))) ≡-refl) ⟩
    unbox
      (wkTm (subst (_ ⊆_) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (factorWk e (factorWk e' w))) t)
      (extRAssoc (subst₂ (CExt _) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (rCtxAbsorbsUpLFExt e (factorWk e' w)) (upLFExt (factorExt e (factorWk e' w)))) (factorExt e' w))
      -- pull out substs
      ≡⟨ cong₂ unbox (≡-sym (subst-application′ (_ ⊆_) (λ x → wkTm x t) (lCtxAbsorbsUpLFExt e (factorWk e' w)))) (ExtIsProp _ _) ⟩
    unbox
      (subst (λ ΓL → Tm ΓL _) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (wkTm (factorWk e (factorWk e' w)) t))
      (subst₂ (λ ΓL ΓR → CExt _ ΓL (ΓR ,, _)) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (rCtxAbsorbsUpLFExt e (factorWk e' w)) (extRAssoc (upLFExt (factorExt e (factorWk e' w))) (factorExt e' w)))
      -- remove substs
      ≡⟨ ≅-to-≡ (cong-unbox≅
        (≡-sym (lCtxAbsorbsUpLFExt e (factorWk e' w))) (cong (_,, _) (≡-sym (rCtxAbsorbsUpLFExt e (factorWk e' w))))
        (≡-subst-removable _ _ _) (≡-subst₂-removable _ _ _ _)) ⟩
    unbox
      (wkTm (factorWk e (factorWk e' w)) t)
      (extRAssoc (upLFExt (factorExt e (factorWk e' w))) (factorExt e' w))
      -- apply shift-unbox
      ≈⟨ ⟶-to-≈ (shift-unbox _ _ _) ⟩
    unbox
      (wkTm (LFExtTo⊆ (factorExt e (factorWk e' w))) (wkTm (factorWk e (factorWk e' w)) t))
      (factorExt e' w)
      -- wkTm preserves composition
      ≡⟨ cong₂ unbox (wkTmPres∙ _ _ _) ≡-refl ⟩
    unbox
      (wkTm (factorWk e (factorWk e' w) ∙ LFExtTo⊆ (factorExt e (factorWk e' w))) t)
      (factorExt e' w)
      -- apply factorisationLemma
      ≡⟨ cong₂ unbox (cong₂ wkTm (≡-sym (factorisationLemma e _)) ≡-refl) ≡-refl ⟩
    unbox
      (wkTm (LFExtTo⊆ e ∙ factorWk e' w) t)
      (factorExt e' w)
      -- wkTm preserves composition
      ≡⟨ cong₂ unbox (≡-sym (wkTmPres∙ _ _ _)) ≡-refl ⟩
    unbox
      (wkTm (factorWk e' w) (wkTm (LFExtTo⊆ e) t))
      (factorExt e' w)
      ≡⟨⟩
    wkTm w (unbox (wkTm (LFExtTo⊆ e) t) e') ∎
  where
  open import Relation.Binary.Reasoning.Setoid (Tm-setoid Γ' a)

wkTmPres≈  : {t t' : Tm Γ a} → (w : Γ ⊆ Γ') → t ≈ t' → wkTm w t ≈ wkTm w t'
wkTmPres≈ w ε            = ε
wkTmPres≈ w (inj₁ x ◅ r) = ≈-trans (invRed w x) (wkTmPres≈ w r)
wkTmPres≈ w (inj₂ y ◅ r) = ≈-trans (≈-sym (invRed w y)) (wkTmPres≈ w r)

wkSubPres≈  : {s s' : Sub Δ Γ} → (w : Δ ⊆ Δ') → s ≈ₛ s' → wkSub w s ≈ₛ wkSub w s'
wkSubPres≈ w ≈ₛ-refl         = ≈ₛ-refl
wkSubPres≈ w (≈ₛ-trans r r') = ≈ₛ-trans (wkSubPres≈ w r) (wkSubPres≈ w r')
wkSubPres≈ w (≈ₛ-sym r)      = ≈ₛ-sym (wkSubPres≈ w r)
wkSubPres≈ w (cong-`,≈ₛ r r') = cong-`,≈ₛ (wkSubPres≈ w r) (wkTmPres≈ w r')
wkSubPres≈ w (cong-lock≈ₛ r) = cong-lock≈ₛ (wkSubPres≈ _ r)
wkSubPres≈ {Δ} {Γ} {Δ'} w (shift-lock≈ₛ {s = s} {e = e} {e' = e'}) = begin
  wkSub w (lock s (extRAssoc (upLFExt e) e'))
     ≡⟨⟩
  lock
    (wkSub (factorWk (extRAssoc (upLFExt e) e') w) s)
    (factorExt (extRAssoc (upLFExt e) e') w)
    -- add substs
    ≡⟨ HE.≅-to-≡ (cong-lock≅ (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w) (≡-subst-addable _ _ _) (≡-subst₂-addable _ _ _ _)) ⟩
  lock
    (subst (λ ΓL → Sub ΓL _) (lCtxPresTrans (upLFExt e) e' w) (wkSub (factorWk (extRAssoc (upLFExt e) e') w) s))
    (subst₂ (CExt _) (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w) (factorExt (extRAssoc (upLFExt e) e') w))
    -- push subst on subterm inside
    ≡⟨ cong₂ lock (subst-application′ (_ ⊆_) (λ w → wkSub w s) (lCtxPresTrans (upLFExt e) e' w)) ≡-refl ⟩
  lock
    (wkSub (subst (_ ⊆_) (lCtxPresTrans (upLFExt e) e' w) (factorWk (extRAssoc (upLFExt e) e') w)) s)
    (subst₂ (CExt _) (lCtxPresTrans (upLFExt e) e' w) (rCtxPresTrans (upLFExt e) e' w) (factorExt (extRAssoc (upLFExt e) e') w))
    -- factorisation preserves transitivity
    ≡⟨ cong₂ lock (cong₂ wkSub (factorWkPresTrans (upLFExt e) e' w) ≡-refl) (factorExtPresTrans (upLFExt e) _ _) ⟩
  lock
    (wkSub (factorWk (upLFExt e) (factorWk e' w)) s)
    (extRAssoc (factorExt (upLFExt e) (factorWk e' w)) (factorExt e' w))
    -- apply equalities for absorption of upLFExt
    ≡⟨ cong₂ lock (cong₂ wkSub (≡-sym (factorWkAbsorbsUpLFExt e (factorWk e' w))) ≡-refl) (cong₂ extRAssoc (≡-sym (factorExtAbsorbsUpLFExt e (factorWk e' w))) ≡-refl) ⟩
  lock
    (wkSub (subst (_ ⊆_) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (factorWk e (factorWk e' w))) s)
    (extRAssoc (subst₂ (CExt _) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (rCtxAbsorbsUpLFExt e (factorWk e' w)) (upLFExt (factorExt e (factorWk e' w)))) (factorExt e' w))
    -- pull out substs
    ≡⟨ cong₂ lock (≡-sym (subst-application′ (_ ⊆_) (λ x → wkSub x s) (lCtxAbsorbsUpLFExt e (factorWk e' w)))) (ExtIsProp _ _) ⟩
  lock
    (subst (λ ΓL → Sub ΓL _) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (wkSub (factorWk e (factorWk e' w)) s))
    (subst₂ (λ ΓL ΓR → CExt _ ΓL (ΓR ,, _)) (lCtxAbsorbsUpLFExt e (factorWk e' w)) (rCtxAbsorbsUpLFExt e (factorWk e' w)) (extRAssoc (upLFExt (factorExt e (factorWk e' w))) (factorExt e' w)))
    -- remove substs
    ≡⟨ HE.≅-to-≡ (cong-lock≅ (≡-sym (lCtxAbsorbsUpLFExt e (factorWk e' w))) (≡-sym (cong (_,, _) (rCtxAbsorbsUpLFExt e (factorWk e' w)))) (≡-subst-removable _ _ _) (≡-subst₂-removable _ _ _ _)) ⟩
  lock
   (wkSub (factorWk e (factorWk e' w)) s)
   (extRAssoc (upLFExt (factorExt e (factorWk e' w))) (factorExt e' w))
   -- apply shift-lock≈ₛ
   ≈⟨ shift-lock≈ₛ ⟩
  lock
   (wkSub (LFExtTo⊆ (factorExt e (factorWk e' w))) (wkSub (factorWk e (factorWk e' w)) s))
   (factorExt e' w)
   -- wkSub preserves composition
   ≡⟨ cong₂ lock (wkSubPres∙ _ _ _) ≡-refl ⟩
  lock
   (wkSub (factorWk e (factorWk e' w) ∙ LFExtTo⊆ (factorExt e (factorWk e' w))) s)
   (factorExt e' w)
   -- apply factorisation lemma
   ≡⟨ cong₂ lock (cong₂ wkSub (≡-sym (factorisationLemma e _)) ≡-refl) ≡-refl ⟩
  lock
   (wkSub (LFExtTo⊆ e ∙ factorWk e' w) s)
   (factorExt e' w)
   -- wkSub preserves composition
   ≡⟨ cong₂ lock (≡-sym (wkSubPres∙ _ _ _)) ≡-refl ⟩
  lock
   (wkSub (factorWk e' w) (wkSub (LFExtTo⊆ e) s))
   (factorExt e' w)
   ≡⟨⟩
  wkSub w (lock (wkSub (LFExtTo⊆ e) s) e') ∎
  where
  open import Relation.Binary.Reasoning.Setoid (Sub-setoid Δ' Γ)

fact-ext≅ : (e : CExt Γ ΓL ΓR)
  → e ≅ extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ)
fact-ext≅ e = ≅-trans
  (≡-subst-addable _ _ _)
  (≡-to-≅ (ExtIsProp′ e (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))))

substTmPresId : (t : Tm Γ a) → t ≈ substTm idₛ t
substTmPresId (var x)     = ≡-to-≈ (≡-sym (substVarPresId x))
substTmPresId (lam t)     = cong-lam≈ (substTmPresId t)
substTmPresId (app t u)   = cong-app≈ (substTmPresId t) (substTmPresId u)
substTmPresId (box t)     = cong-box≈ (substTmPresId t)
substTmPresId (unbox t e) = fact-unbox≈ t e
  where
  --
  coh-wkTm-substTm : (t : Tm Γ a) (w : Γ ⊆ Γ') → wkTm w t ≈ substTm (embWk w) t
  coh-wkTm-substTm {a = a} {Γ' = Γ'} t w = begin
    wkTm w t
      -- apply IH
      ≈⟨ wkTmPres≈ w (substTmPresId t) ⟩
    wkTm w (substTm idₛ t)
      -- apply naturality of substTm
      ≡⟨ ≡-sym (nat-substTm t idₛ w) ⟩
    substTm (wkSub w idₛ) t
      -- weakening id subst is same as embedding the weakening into a subst
      ≡⟨ cong₂ substTm {u = t} (wkSubId w) ≡-refl ⟩
    substTm (embWk w) t ∎
    where
    open import Relation.Binary.Reasoning.Setoid (Tm-setoid Γ' a)
  --
  fact-unbox≈ : (t : Tm ΓL (◻ a)) (e : CExt Γ ΓL ΓR)
    → unbox t e ≈ unbox (substTm (factorSubₛ e idₛ) t) (factorExtₛ e idₛ)
  fact-unbox≈ {a = a} {Γ = Γ} t e = begin
    unbox t e
      -- expand extension e
      ≡⟨ ≅-to-≡ (cong-unbox≅ ≡-refl (extRUniq e (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))) ≅-refl (fact-ext≅ e)) ⟩
    unbox t (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))
      -- apply shift-unbox
      ≈⟨ ⟶-to-≈ (shift-unbox _ _ _) ⟩
    unbox (wkTm (LFExtTo⊆ (factorSubₛIdWk e)) t) (factorExtₛ e idₛ)
      -- rewrite wkTm to substTm
      ≈⟨ cong-unbox1≈ (coh-wkTm-substTm t _) ⟩
    unbox (substTm (embWk (LFExtTo⊆ (factorSubₛIdWk e))) t) (factorExtₛ e idₛ)
      -- show that the subst is the factorisation of the id subst
      ≡⟨ cong₂ unbox (cong₂ substTm {u = t} (≡-sym (factorSubₛIdWkIsFactorSubₛId e)) ≡-refl) ≡-refl ⟩
    unbox (substTm (factorSubₛ e idₛ) t) (factorExtₛ e idₛ) ∎
    where
    open import Relation.Binary.Reasoning.Setoid (Tm-setoid Γ a)

rightIdSub : (s : Sub Γ Γ') → s ≈ₛ (s ∙ₛ idₛ)
rightIdSub []         = ≈ₛ-refl
rightIdSub (s `, t)   = cong-`,≈ₛ (rightIdSub s) (substTmPresId t)
rightIdSub (lock s e) = fact-lock≈ s e
  where
  --
  fact-lock≈ : (s : Sub ΓL Δ) (e : CExt Γ ΓL ΓR)
    → lock s e ≈ₛ lock (s ∙ₛ factorSubₛ e idₛ) (factorExtₛ e idₛ)
  fact-lock≈ {Δ = Δ} {Γ = Γ} s e = begin
    lock s e
      -- expand extension e
      ≡⟨ HE.≅-to-≡ (cong-lock≅ ≡-refl (extRUniq e (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))) ≅-refl (fact-ext≅ e)) ⟩
    lock s (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))
      -- apply shift-lock≈ₛ
      ≈⟨ shift-lock≈ₛ ⟩
    lock (wkSub (LFExtTo⊆ (factorSubₛIdWk e)) s) (factorExtₛ e idₛ)
      -- apply IH
      ≈⟨ cong-lock≈ₛ (wkSubPres≈ _ (rightIdSub s)) ⟩
    lock (wkSub (LFExtTo⊆ (factorSubₛIdWk e)) (s ∙ₛ idₛ)) (factorExtₛ e idₛ)
      -- rewrite using coherence between weakening and composing substs (associativity, really)
      ≡⟨ cong₂ lock (coh-wkSub-∙ₛ s idₛ (LFExtTo⊆ (factorSubₛIdWk e))) ≡-refl ⟩
    lock (s ∙ₛ wkSub (LFExtTo⊆ (factorSubₛIdWk e)) idₛ) (factorExtₛ e idₛ)
      --  weakening of id subst is itself a weakening
      ≡⟨ cong₂ lock (cong (s ∙ₛ_) (wkSubId _)) ≡-refl ⟩
    lock (s ∙ₛ (embWk (LFExtTo⊆ (factorSubₛIdWk e)))) (factorExtₛ e idₛ)
      -- show that the weakening subst is the factorisation of the id subst
      ≡⟨ cong₂ lock (cong (s ∙ₛ_) (≡-sym (factorSubₛIdWkIsFactorSubₛId e))) ≡-refl ⟩
    lock (s ∙ₛ factorSubₛ e idₛ) (factorExtₛ e idₛ) ∎
    where
    open import Relation.Binary.Reasoning.Setoid (Sub-setoid Γ (Δ 🔒))

substVarPres≈ : {s s' : Sub Δ Γ} (v : Var Γ a) → s ≈ₛ s' → substVar s v ≈ substVar s' v
substVarPres≈ v      ≈ₛ-refl          = ≈-refl
substVarPres≈ v      (≈ₛ-trans r r')  = ≈-trans (substVarPres≈ v r) (substVarPres≈ v r')
substVarPres≈ v      (≈ₛ-sym r)       = ≈-sym (substVarPres≈ v r)
substVarPres≈ ze     (cong-`,≈ₛ r r') = r'
substVarPres≈ (su v) (cong-`,≈ₛ r x)  = substVarPres≈ v r

substTmPres≈ : {s s' : Sub Δ Γ} (t : Tm Γ a) → s ≈ₛ s' → substTm s t ≈ substTm s' t
substTmPres≈ (var v)     r = substVarPres≈ v r
substTmPres≈ (lam t)     r = cong-lam≈ (substTmPres≈ t (cong-`,≈ₛ (wkSubPres≈ fresh r) ≈-refl))
substTmPres≈ (app t u)   r = cong-app≈ (substTmPres≈ t r) (substTmPres≈ u r)
substTmPres≈ (box t)     r = cong-box≈ (substTmPres≈ t (cong-lock≈ₛ r))
substTmPres≈ (unbox t e) r = {!!}

--------------------
-- Derived equations
--------------------
