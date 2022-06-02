{-# OPTIONS --safe --with-K #-}
module IK.Term where

open import IK.Term.Base       public
open import IK.Term.Conversion public
open import IK.Term.NormalForm public
open import IK.Term.Properties public
open import IK.Term.Reduction  public

pattern var0 = var v0
pattern var1 = var v1
pattern var2 = var v2
