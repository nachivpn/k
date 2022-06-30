{-# OPTIONS --without-K #-}
module IK.Applications.WeakNorm where

open import Data.Empty
open import Data.Unit
open import Data.Product using (Σ ; _×_ ; _,_ ; ∃ ; ∃₂)

open import Relation.Nullary

open import IK.Norm.Base
open import IK.Norm.Properties.Soundness.Trace

open import IK.Term

-- defines a beta-reduction relation (_⟶β_)
BetaRule : {t u : Tm Γ a} → t ⟶ u → Set
BetaRule red-fun        = ⊤
BetaRule exp-fun        = ⊥
BetaRule red-box        = ⊤
BetaRule exp-box        = ⊥
BetaRule (cong-lam r)   = BetaRule r
BetaRule (cong-app1 r)  = BetaRule r
BetaRule (cong-app2 r)  = BetaRule r
BetaRule (cong-box r)   = BetaRule r
BetaRule (cong-unbox r) = BetaRule r

BetaShort : Tm Γ a → Set
BetaShort {Γ} {a} t = {t' : Tm Γ a} → ¬ Σ (t ⟶ t') BetaRule

neBetaShort : (n : Ne Γ a) → BetaShort (embNe n)
nfBetaShort : (n : Nf Γ a) → BetaShort (embNf n)

neBetaShort (app (var _) m)        (cong-app2 r , p)  = nfBetaShort m (r , p)
neBetaShort (app (app n m') m)     (cong-app1 r , p)  = neBetaShort (app n m') (r , p)
neBetaShort (app (app n m') m)     (cong-app2 r , p)  = nfBetaShort m (r , p)
neBetaShort (app (unbox n m') m)   (cong-app1 r , p)  = neBetaShort (unbox n m') (r , p)
neBetaShort (app (unbox n m') m)   (cong-app2 r , p)  = nfBetaShort m (r , p)
neBetaShort (unbox (app n m') m)   (cong-unbox r , p) = neBetaShort (app n m') (r , p)
neBetaShort (unbox (unbox n m') m) (cong-unbox r , p) = neBetaShort (unbox n m') (r , p)
neBetaShort (var x)                (exp-fun , p)      = p
neBetaShort (var x)                (exp-box , p)      = p
neBetaShort (app (var x) _)        (cong-app1 r , p)  = neBetaShort (var x) (r , p)
neBetaShort (app (app n m) _)      (exp-fun , p)      = p
neBetaShort (app (app n m) _)      (exp-box , p)      = p
neBetaShort (unbox (var x) _)      (cong-unbox r , p) = neBetaShort (var x) (r , p)
neBetaShort (unbox (var x) _)      (exp-fun , p)      = p
neBetaShort (unbox (var x) _)      (exp-box , p)      = p
neBetaShort (unbox (app n m) _)    (exp-fun , p)      = p
neBetaShort (unbox (app n m) _)    (exp-box , p)      = p
neBetaShort (unbox (unbox n e) _)  (exp-fun , p)      = p
neBetaShort (unbox (unbox n e) _)  (exp-box , p)      = p

nfBetaShort (up  x)                (r , p)            = neBetaShort x (r , p)
nfBetaShort (lam n)                (cong-lam r , p)   = nfBetaShort n (r , p)
nfBetaShort (box n)                (cong-box r , p)   = nfBetaShort n (r , p)

-- defines an eta-expansion relation (_⟶η_)
-- TODO: this definition could be very wrong, need to check this up!
EtaRule : (t : Tm Γ a) → {u : Tm Γ a} → t ⟶ u → Set
EtaRule _       red-fun          = ⊥
EtaRule _       red-box          = ⊥
EtaRule (lam t) exp-fun          = ⊥
EtaRule (box t) exp-box          = ⊥
EtaRule _       (cong-app1 r)    = ⊥
EtaRule _       (cong-unbox r)   = ⊥
EtaRule _       exp-fun          = ⊤
EtaRule _       exp-box          = ⊤
EtaRule _       (cong-lam r)     = EtaRule _ r
EtaRule _       (cong-app2 r)    = EtaRule _ r
EtaRule _       (cong-box r)     = EtaRule _ r

-- NOTE: Eta expansion must not create a β-redex, thus they
-- cannot be performed on constructors (lam, box)
-- or in an elimination frame (app [.] m, unbox [.] e)
-- c.f. η-rules in "Extensional rewriting with sums" by Lindley (after Proposition 4)

EtaLong : Tm Γ a → Set
EtaLong {Γ} {a} t = {t' : Tm Γ a} → ¬ Σ (t ⟶ t') (EtaRule t)

-- Note: not all neutrals are eta-long, only ones of base type
neEtaLong : (n : Ne Γ ι) → EtaLong (embNe n)
nfEtaLong : (n : Nf Γ a) → EtaLong (embNf n)

neEtaLong (app (var _) m)       (cong-app2 r , p)  = nfEtaLong m (r , p)
neEtaLong (app (app _ _) m)     (cong-app2 r , p)  = nfEtaLong m (r , p)
neEtaLong (app (unbox _ _) m)   (cong-app2 r , p)  = nfEtaLong m (r , p)
neEtaLong (unbox (var _) _)     (cong-unbox r , p) = p
neEtaLong (unbox (app _ _) _)   (cong-unbox r , p) = p
neEtaLong (unbox (unbox _ _) _) (cong-unbox r , p) = p

nfEtaLong (up  x) (r , p)          = neEtaLong x (r , p)
nfEtaLong (lam _) (exp-fun , p)    = p
nfEtaLong (lam n) (cong-lam r , p) = nfEtaLong n (r , p)
nfEtaLong (box _) (exp-box , p)    = p
nfEtaLong (box n) (cong-box r , p) = nfEtaLong n (r , p)

BetaEtaNormal : (t : Tm Γ a) → Set
BetaEtaNormal t = BetaShort t × EtaLong t

WeakNorm : (t : Tm Γ a) → Set
WeakNorm {Γ} {a} t = Σ (Nf Γ a) λ n → (t ⟶* embNf n) × BetaEtaNormal (embNf n)

weakNorm : (t : Tm Γ a) → WeakNorm t
weakNorm t = n , trace t , nfBetaShort n , nfEtaLong n
  where n = norm t
