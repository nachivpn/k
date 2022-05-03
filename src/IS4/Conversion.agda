module IS4.Conversion where

open import HEUtil
open import IS4.Term
open import IS4.Reduction
  as Reduction
open import IS4.HellOfSyntacticLemmas

open import Data.Product
  using (Σ ; _,_)
module _ {a} {b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} where
  open import Function
  open import Data.Product.Properties
  open Inverse (Σ-≡,≡↔≡ {p₁ = p₁} {p₂ = p₂}) public
    using    ()
    renaming (f to Σ-≡,≡→≡)

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
  using    (_≡_ ; cong ; cong₂ ; subst ; subst₂ ; module ≡-Reasoning)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)
module _ {a} {A : Set a} where
  ≡-trans˘ : ∀ {x y z : A} → y ≡ x → y ≡ z → x ≡ z
  ≡-trans˘ y≡x y≡z = ≡-trans (≡-sym y≡x) y≡z

import Relation.Binary.Reasoning.Setoid
  as SetoidReasoning
module RelReasoning {a} {A : Set a} {r} (R : A → A → Set r) where
  ≡-step-≡ : ∀ {x'} {x} {y} {y'} → x' ≡ x → R x y → y ≡ y' → R x' y'
  ≡-step-≡ ≡-refl r ≡-refl = r

  step-≡ : ∀ {x} {y} {y'} → R x y → y ≡ y' → R x y'
  step-≡ = ≡-step-≡ ≡-refl

open import Relation.Binary.HeterogeneousEquality as HE
  using    (_≅_)
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
    renaming (refl to ≈-refl ; reflexive to ≈-reflexive ; sym to ≈-sym ; trans to ≈-trans ; isEquivalence to ≈-equiv)

  ≈-reflexive˘ : t' ≡ t → t ≈ t'
  ≈-reflexive˘ t'≡t = ≈-reflexive (≡-sym t'≡t)

  ≈-trans˘ : t' ≈ t → t' ≈ t'' → t ≈ t''
  ≈-trans˘ t'≈t t'≈t'' = ≈-trans (≈-sym t'≈t) t'≈t''

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

cong-unbox2≈ : ∀ {t : Tm Γ (◻ a)} {e : CExt Δ Γ ΓR} {e' : CExt Δ Γ ΓR'} → unbox t e ≈ unbox t e'
cong-unbox2≈ {t = t} {e} {e'} = subst (λ (_ , e') → unbox t e ≈ unbox t e') (Σ-≡,≡→≡ (extRUniq e e' , ExtIsProp′ e e')) ≈-refl

cong-unbox≈ : ∀ (t≈t' : t ≈ t') → unbox t e ≈ unbox t' e'
cong-unbox≈ t≈t' = ≈-trans (cong-unbox1≈ t≈t') cong-unbox2≈

shift-unbox≈ : ∀ (t : Tm Γ (◻ a)) (w : LFExt Γ' Γ ΓR) → unbox t e ≈ unbox (wkTm (LFExtTo⊆ w) t) e'
shift-unbox≈ t w = ≈-trans cong-unbox2≈ (⟶-to-≈ (Reduction.shift-unbox t w _))

----------------------------------------------------------------------
-- Congruence closure of the relation that identifies substitutions up
-- to "built-in" weakenings (see `shift-lock≈ₛ`)
----------------------------------------------------------------------

data _⟶ₛ_ : Sub Δ Γ → Sub Δ Γ → Set where
  cong-`,⟶ₛ1   : {s s' : Sub Δ Γ} {t : Tm Δ a}
    → s ⟶ₛ s' → (s `, t) ⟶ₛ (s' `, t)
  cong-`,⟶ₛ2   : {s : Sub Δ Γ} {t t' : Tm Δ a}
    → t ≈ t' → (s `, t) ⟶ₛ (s `, t')
  cong-lock⟶ₛ  : {s s' : Sub ΔL ΓL} {e : CExt Δ ΔL ΔR}
    → s ⟶ₛ s' → lock s e ⟶ₛ lock s' e
  shift-lock⟶ₛ : {ΔLL ΔLR : Ctx} {s : Sub ΔLL Γ} (w : LFExt ΔL ΔLL ΔLR) {e : CExt Δ ΔL ΔR}
    → lock s (extRAssoc (upLFExt w) e) ⟶ₛ lock (wkSub (LFExtTo⊆ w) s) e

Sub-setoid : (Δ Γ : Ctx) → Setoid _ _
Sub-setoid Δ Γ = setoid (_⟶ₛ_ {Δ} {Γ})

module _ {Δ Γ : Ctx} where
  open Setoid (Sub-setoid Δ Γ) public
    using ()
    renaming (_≈_ to _≈ₛ_ ; reflexive to ≈ₛ-reflexive ; refl to ≈ₛ-refl ; sym to ≈ₛ-sym ; trans to ≈ₛ-trans)

  ≈ₛ-reflexive˘ : σ' ≡ σ → σ ≈ₛ σ'
  ≈ₛ-reflexive˘ σ'≡σ = ≈ₛ-reflexive (≡-sym σ'≡σ)

⟶ₛ-to-≈ₛ : σ ⟶ₛ σ' → σ ≈ₛ σ'
⟶ₛ-to-≈ₛ p = inj₁ p ◅ ε

module _ {σ : Sub Δ Γ → Sub Δ' Γ'} (cong-σ : ∀ {τ τ' : Sub Δ Γ} → (τ⟶τ' : τ ⟶ₛ τ') → σ τ ⟶ₛ σ τ') where
  -- XXX: fold
  cong-⟶ₛ-to-cong-≈ₛ : ∀ (τ≈τ' : τ ≈ₛ τ') → σ τ ≈ₛ σ τ'
  cong-⟶ₛ-to-cong-≈ₛ ε                     = ε
  cong-⟶ₛ-to-cong-≈ₛ (inj₁ τ⟶τ'' ◅ τ''≈τ') = inj₁ (cong-σ τ⟶τ'') ◅ cong-⟶ₛ-to-cong-≈ₛ τ''≈τ'
  cong-⟶ₛ-to-cong-≈ₛ (inj₂ τ⟵τ'' ◅ τ''≈τ') = inj₂ (cong-σ τ⟵τ'') ◅ cong-⟶ₛ-to-cong-≈ₛ τ''≈τ'

cong-`,1≈ₛ : (σ≈σ' : σ ≈ₛ σ') → (σ `, t) ≈ₛ (σ' `, t)
cong-`,1≈ₛ = cong-⟶ₛ-to-cong-≈ₛ cong-`,⟶ₛ1

cong-`,2≈ₛ : (t≈t' : t ≈ t') → (σ `, t) ≈ₛ (σ `, t')
cong-`,2≈ₛ t≈t' = ⟶ₛ-to-≈ₛ (cong-`,⟶ₛ2 t≈t')

cong-`,≈ₛ : (σ≈σ' : σ ≈ₛ σ') → (t≈t' : t ≈ t') → (σ `, t) ≈ₛ (σ' `, t')
cong-`,≈ₛ σ≈σ' t≈t' = ≈ₛ-trans (cong-`,1≈ₛ σ≈σ') (cong-`,2≈ₛ t≈t')

cong-lock≈ₛ : (σ≈σ' : σ ≈ₛ σ') → lock σ e ≈ₛ lock σ' e
cong-lock≈ₛ = cong-⟶ₛ-to-cong-≈ₛ cong-lock⟶ₛ

shift-lock≈ₛ : (w : LFExt Δ' Δ ΔR) → lock σ (extRAssoc (upLFExt w) e) ≈ₛ lock (wkSub (LFExtTo⊆ w) σ) e
shift-lock≈ₛ w = ⟶ₛ-to-≈ₛ (shift-lock⟶ₛ w)

---------
-- Lemmas
---------

module _ where
  module _ {Γ} {a} where
    open RelReasoning (_⟶_ {Γ} {a}) public

  wkTmPres⟶ : (w : Γ ⊆ Γ') → t ⟶ t' → wkTm w t ⟶ wkTm w t'
  wkTmPres⟶ w (red-fun t u)
    = step-≡ (red-fun _ _) (beta-wk-lemma w u t)
  wkTmPres⟶ w (exp-fun _)
    = step-≡ (exp-fun _) (cong lam (cong₂ app keepFreshLemma ≡-refl))
  wkTmPres⟶ w (red-box t e)
    = step-≡
      (red-box _ _)
      (≡-trans
        (≡-trans˘
          (coh-trimSub-wkTm t _ _)
          (cong
            (λ s → substTm (lock s (factorExt e w)) t)
            (≡-trans
              (trimSubId (factorWk e w))
              (≡-sym (wkSubId _)))))
        (nat-substTm t _ _))
  wkTmPres⟶ w (exp-box _)
    = exp-box _
  wkTmPres⟶ w (cong-lam r)
    = cong-lam (wkTmPres⟶ (keep w) r)
  wkTmPres⟶ w (cong-box r)
    = cong-box (wkTmPres⟶ (keep🔒 w) r)
  wkTmPres⟶ w (cong-unbox {e = e} r)
    = cong-unbox (wkTmPres⟶ (factorWk e w ) r)
  wkTmPres⟶ w (cong-app1 r)
    = cong-app1 (wkTmPres⟶ w r)
  wkTmPres⟶ w (cong-app2 r)
    = cong-app2 (wkTmPres⟶ w r)
  wkTmPres⟶ w (shift-unbox t e e')
    = ≡-step-≡
      (let open ≡-Reasoning in begin
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
        (extRAssoc (upLFExt (factorExt e (factorWk e' w))) (factorExt e' w)) ∎)
      (shift-unbox _ _ _)
      (let open ≡-Reasoning in begin
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
      wkTm w (unbox (wkTm (LFExtTo⊆ e) t) e') ∎)

wkTmPres≈ : (w : Γ ⊆ Γ') → t ≈ t' → wkTm w t ≈ wkTm w t'
wkTmPres≈ w = cong-⟶-to-cong-≈ (wkTmPres⟶ w)

wkSubPres⟶ : (w : Δ ⊆ Δ') → σ ⟶ₛ σ' → wkSub w σ ⟶ₛ wkSub w σ'
wkSubPres⟶ w (cong-`,⟶ₛ1 r) = cong-`,⟶ₛ1 (wkSubPres⟶ w r)
wkSubPres⟶ w (cong-`,⟶ₛ2 r) = cong-`,⟶ₛ2 (wkTmPres≈ w r)
wkSubPres⟶ w (cong-lock⟶ₛ r) = cong-lock⟶ₛ (wkSubPres⟶ _ r)
wkSubPres⟶ w (shift-lock⟶ₛ {s = s} w' {e}) = RelReasoning.≡-step-≡ _⟶ₛ_
  (let open ≡-Reasoning in begin
  wkSub w (lock s (extRAssoc (upLFExt w') e))
     ≡⟨⟩
  lock
    (wkSub (factorWk (extRAssoc (upLFExt w') e) w) s)
    (factorExt (extRAssoc (upLFExt w') e) w)
    -- add substs
    ≡⟨ HE.≅-to-≡ (cong-lock≅ (lCtxPresTrans (upLFExt w') e w) (rCtxPresTrans (upLFExt w') e w) (≡-subst-addable _ _ _) (≡-subst₂-addable _ _ _ _)) ⟩
  lock
    (subst (λ ΓL → Sub ΓL _) (lCtxPresTrans (upLFExt w') e w) (wkSub (factorWk (extRAssoc (upLFExt w') e) w) s))
    (subst₂ (CExt _) (lCtxPresTrans (upLFExt w') e w) (rCtxPresTrans (upLFExt w') e w) (factorExt (extRAssoc (upLFExt w') e) w))
    -- push subst on subterm inside
    ≡⟨ cong₂ lock (subst-application′ (_ ⊆_) (λ w → wkSub w s) (lCtxPresTrans (upLFExt w') e w)) ≡-refl ⟩
  lock
    (wkSub (subst (_ ⊆_) (lCtxPresTrans (upLFExt w') e w) (factorWk (extRAssoc (upLFExt w') e) w)) s)
    (subst₂ (CExt _) (lCtxPresTrans (upLFExt w') e w) (rCtxPresTrans (upLFExt w') e w) (factorExt (extRAssoc (upLFExt w') e) w))
    -- factorisation preserves transitivity
    ≡⟨ cong₂ lock (cong₂ wkSub (factorWkPresTrans (upLFExt w') e w) ≡-refl) (factorExtPresTrans (upLFExt w') _ _) ⟩
  lock
    (wkSub (factorWk (upLFExt w') (factorWk e w)) s)
    (extRAssoc (factorExt (upLFExt w') (factorWk e w)) (factorExt e w))
    -- apply equalities for absorption of upLFExt
    ≡⟨ cong₂ lock (cong₂ wkSub (≡-sym (factorWkAbsorbsUpLFExt w' (factorWk e w))) ≡-refl) (cong₂ extRAssoc (≡-sym (factorExtAbsorbsUpLFExt w' (factorWk e w))) ≡-refl) ⟩
  lock
    (wkSub (subst (_ ⊆_) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (factorWk w' (factorWk e w))) s)
    (extRAssoc (subst₂ (CExt _) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (rCtxAbsorbsUpLFExt w' (factorWk e w)) (upLFExt (factorExt w' (factorWk e w)))) (factorExt e w))
    -- pull out substs
    ≡⟨ cong₂ lock (≡-sym (subst-application′ (_ ⊆_) (λ x → wkSub x s) (lCtxAbsorbsUpLFExt w' (factorWk e w)))) (ExtIsProp _ _) ⟩
  lock
    (subst (λ ΓL → Sub ΓL _) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (wkSub (factorWk w' (factorWk e w)) s))
    (subst₂ (λ ΓL ΓR → CExt _ ΓL (ΓR ,, _)) (lCtxAbsorbsUpLFExt w' (factorWk e w)) (rCtxAbsorbsUpLFExt w' (factorWk e w)) (extRAssoc (upLFExt (factorExt w' (factorWk e w))) (factorExt e w)))
    -- remove substs
    ≡⟨ HE.≅-to-≡ (cong-lock≅ (≡-sym (lCtxAbsorbsUpLFExt w' (factorWk e w))) (≡-sym (cong (_,, _) (rCtxAbsorbsUpLFExt w' (factorWk e w)))) (≡-subst-removable _ _ _) (≡-subst₂-removable _ _ _ _)) ⟩
  lock
   (wkSub (factorWk w' (factorWk e w)) s)
   (extRAssoc (upLFExt (factorExt w' (factorWk e w))) (factorExt e w)) ∎)
  (shift-lock⟶ₛ _)
  (let open ≡-Reasoning in begin
  lock
   (wkSub (LFExtTo⊆ (factorExt w' (factorWk e w))) (wkSub (factorWk w' (factorWk e w)) s))
   (factorExt e w)
   -- wkSub preserves composition
   ≡⟨ cong₂ lock (wkSubPres∙ _ _ _) ≡-refl ⟩
  lock
   (wkSub (factorWk w' (factorWk e w) ∙ LFExtTo⊆ (factorExt w' (factorWk e w))) s)
   (factorExt e w)
   -- apply factorisation lemma
   ≡⟨ cong₂ lock (cong₂ wkSub (≡-sym (factorisationLemma w' _)) ≡-refl) ≡-refl ⟩
  lock
   (wkSub (LFExtTo⊆ w' ∙ factorWk e w) s)
   (factorExt e w)
   -- wkSub preserves composition
   ≡⟨ cong₂ lock (≡-sym (wkSubPres∙ _ _ _)) ≡-refl ⟩
  lock
   (wkSub (factorWk e w) (wkSub (LFExtTo⊆ w') s))
   (factorExt e w)
   ≡⟨⟩
  wkSub w (lock (wkSub (LFExtTo⊆ w') s) e) ∎)

wkSubPres≈ : (w : Δ ⊆ Δ') → σ ≈ₛ σ' → wkSub w σ ≈ₛ wkSub w σ'
wkSubPres≈ w = cong-⟶ₛ-to-cong-≈ₛ (wkSubPres⟶ w)

fact-ext≅ : (e : CExt Γ ΓL ΓR)
  → e ≅ extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ)
fact-ext≅ e = ≅-trans
  (≡-subst-addable _ _ _)
  (≡-to-≅ (ExtIsProp′ e (extRAssoc (upLFExt (factorSubₛIdWk e)) (factorExtₛ e idₛ))))

substTmPresId : (t : Tm Γ a) → t ≈ substTm idₛ t
substTmPresId (var x)     = ≈-reflexive˘ (substVarPresId x)
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
    open SetoidReasoning (Tm-setoid Γ' a)
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
    open SetoidReasoning (Tm-setoid Γ a)

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
      ≈⟨ shift-lock≈ₛ _ ⟩
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
    open SetoidReasoning (Sub-setoid Γ (Δ 🔒))

substVarPres⟶ : (v : Var Γ a) → σ ⟶ₛ σ' → substVar σ v ≈ substVar σ' v
substVarPres⟶ ze     (cong-`,⟶ₛ1 s⟶s') = ≈-refl
substVarPres⟶ ze     (cong-`,⟶ₛ2 t≈t') = t≈t'
substVarPres⟶ (su v) (cong-`,⟶ₛ1 s⟶s') = substVarPres⟶ v s⟶s'
substVarPres⟶ (su v) (cong-`,⟶ₛ2 t≈t') = ≈-refl

-- XXX: fold
substVarPres≈ : (v : Var Γ a) → σ ≈ₛ σ' → substVar σ v ≈ substVar σ' v
substVarPres≈ v ε                    = ≈-refl
substVarPres≈ v (inj₁ σ⟶σ' ◅ σ'≈σ'') = ≈-trans (substVarPres⟶ v σ⟶σ') (substVarPres≈ v σ'≈σ'')
substVarPres≈ v (inj₂ σ'⟶σ ◅ σ≈σ'')  = ≈-trans˘ (substVarPres⟶ v σ'⟶σ) (substVarPres≈ v σ≈σ'')

substTmPres⟶ : (t : Tm Γ a) → σ ⟶ₛ σ' → substTm σ t ≈ substTm σ' t
substTmPres⟶ (var v)     r = substVarPres⟶ v r
substTmPres⟶ (lam t)     r = cong-lam≈ (substTmPres⟶ t (cong-`,⟶ₛ1 (wkSubPres⟶ fresh r)))
substTmPres⟶ (app t u)   r = cong-app≈ (substTmPres⟶ t r) (substTmPres⟶ u r)
substTmPres⟶ (box t)     r = cong-box≈ (substTmPres⟶ t (cong-lock⟶ₛ r))
substTmPres⟶ (unbox t e) r = {!!}

-- XXX: fold
substTmPres≈ : (t : Tm Γ a) → (σ≈σ' : σ ≈ₛ σ') → substTm σ t ≈ substTm σ' t
substTmPres≈ t ε                    = ≈-refl
substTmPres≈ t (inj₁ σ⟶σ' ◅ σ'≈σ'') = ≈-trans (substTmPres⟶ t σ⟶σ') (substTmPres≈ t σ'≈σ'')
substTmPres≈ t (inj₂ σ'⟶σ ◅ σ≈σ'')  = ≈-trans˘ (substTmPres⟶ t σ'⟶σ) (substTmPres≈ t σ≈σ'')

--------------------
-- Derived equations
--------------------
