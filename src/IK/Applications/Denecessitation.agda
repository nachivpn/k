module IK.Applications.Denecessitation where

open import Data.Empty

open import IK.Term
open import IK.Norm
open import IK.Applications.Neutrality

private
  variable
    v v' v'' : Var Γ a
    N        : Set
    n n' n'' : N
    m m' m'' : N

data _not-free-in_⊢var_ : (Δ : Ctx) → (Γ : Ctx) → (v : Var (Δ ,, Γ) a) → Set where
  ze : Δ not-free-in (Γ `, a) ⊢var ze
  su : Δ not-free-in Γ ⊢var v → Δ not-free-in (Γ `, b) ⊢var su v

data _not-free-in_⊢Nf_ : (Δ : Ctx) → (Γ : Ctx) → (n : Nf (Δ ,, Γ) a) → Set
data _not-free-in_⊢Ne_ : (Δ : Ctx) → (Γ : Ctx) → (n : Ne (Δ ,, Γ) a) → Set

data _not-free-in_⊢Ne_ where
  var    : Δ not-free-in Γ ⊢var v → Δ not-free-in Γ ⊢Ne var v
  app    : Δ not-free-in Γ ⊢Ne n → Δ not-free-in Γ ⊢Nf m → Δ not-free-in Γ ⊢Ne (app n m)
  unbox₁ : Δ not-free-in Γ  ⊢Ne n → (e : LFExt (Δ ,, (Γ 🔒 ,, Γ')) (Δ ,, Γ 🔒) Γ')        → Δ not-free-in (Γ 🔒 ,, Γ') ⊢Ne (unbox n e)
  unbox₂ : Δ not-free-in [] ⊢Ne n → (e : LFExt (Δ 🔒 ,, Δ' ,, Γ)   (Δ 🔒)      (Δ' ,, Γ)) → (Δ 🔒 ,, Δ') not-free-in Γ ⊢Ne (unbox n e)

data _not-free-in_⊢Nf_ where
  up𝕓 : Δ not-free-in Γ        ⊢Ne n → Δ not-free-in Γ ⊢Nf (up𝕓 n)
  lam : Δ not-free-in (Γ `, a) ⊢Nf n → Δ not-free-in Γ ⊢Nf (lam n)
  box : Δ not-free-in (Γ 🔒)   ⊢Nf n → Δ not-free-in Γ ⊢Nf (box n)

data _not-free-in_⊢_ : (Δ : Ctx) → (Γ : Ctx) → (t : Tm (Δ ,, Γ) a) → Set where
  var    : Δ not-free-in Γ ⊢var v → Δ not-free-in Γ ⊢ var v
  lam    : Δ not-free-in (Γ `, a) ⊢ t → Δ not-free-in Γ ⊢ (lam t)
  app    : Δ not-free-in Γ ⊢ t → Δ not-free-in Γ ⊢ u → Δ not-free-in Γ ⊢ (app t u)
  box    : Δ not-free-in (Γ 🔒) ⊢ t → Δ not-free-in Γ ⊢ (box t)
  unbox₁ : Δ not-free-in Γ  ⊢ t → (e : LFExt (Δ ,, (Γ 🔒 ,, Γ')) (Δ ,, Γ 🔒) Γ')        → Δ not-free-in (Γ 🔒 ,, Γ') ⊢ (unbox t e)
  unbox₂ : Δ not-free-in [] ⊢ t → (e : LFExt (Δ 🔒 ,, Δ' ,, Γ)   (Δ 🔒)      (Δ' ,, Γ)) → (Δ 🔒 ,, Δ') not-free-in Γ ⊢ (unbox t e)

leftUnwkVar : (v : Var (Δ ,, Γ) a) → Δ not-free-in Γ ⊢var v → Var Γ a
leftUnwkVar .ze     ze     = ze
leftUnwkVar .(su _) (su p) = su (leftUnwkVar _ p)

leftUnwkNe : (n : Ne (Δ ,, Γ) a) → Δ not-free-in Γ ⊢Ne n → Ne Γ a
leftUnwkNf : (n : Nf (Δ ,, Γ) a) → Δ not-free-in Γ ⊢Nf n → Nf Γ a

leftUnwkNe (var v)     (var p)       = var (leftUnwkVar v p)
leftUnwkNe (app t u)   (app p q)     = app (leftUnwkNe t p) (leftUnwkNf u q)
leftUnwkNe (unbox t e) (unbox₁ p .e) = unbox (leftUnwkNe t p) (leftUnwkLFExt e)
leftUnwkNe (unbox t e) (unbox₂ p .e) = ⊥-elim (noClosedNe (leftUnwkNe t p))

leftUnwkNf (up𝕓 n) (up𝕓 x) = up𝕓 (leftUnwkNe n x)
leftUnwkNf (lam t) (lam p) = lam (leftUnwkNf t p)
leftUnwkNf (box t) (box p) = box (leftUnwkNf t p)

-- norm-pres-not-free-in : ∀ (t : Tm (Δ ,, Γ) a) → Δ not-free-in Γ ⊢ t → Δ not-free-in Γ ⊢Nf norm t
-- leftUnwkTm : (t : Tm (Δ ,, Γ) a) → Δ not-free-in Γ ⊢ t → Tm Γ a
