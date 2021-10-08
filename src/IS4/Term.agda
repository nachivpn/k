module IS4.Term where

--
-- Implementation of the IS4 (Intuitionistic S4) calculus from
-- "Fitch-Style Modal Lambda Calculi" by Ranald Clouston (2018)
--

open import IS4.Term.Base       public
open import IS4.Term.Conversion public
open import IS4.Term.NormalForm public
open import IS4.Term.Properties public
open import IS4.Term.Reduction  public

pattern var0 = var v0
pattern var1 = var v1
pattern var2 = var v2
