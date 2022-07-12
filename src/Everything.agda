{-# OPTIONS --without-K #-}
module Everything where

import Type
import Context

import IK.Term
import IK.Term.Conversion
import IK.Term.NormalForm
import IK.Term.Reduction

import IK.Norm
import IK.Norm.NbE.Model
import IK.Norm.NbE.Reification
import IK.Norm.Properties.Completeness
import IK.Norm.Properties.Soundness
import IK.Norm.Properties.Soundness.Trace

import IK.Applications.Experiments
import IK.Applications.Neutrality
import IK.Applications.WeakNorm

import IS4.Term
import IS4.Term.Conversion
import IS4.Term.NormalForm
import IS4.Term.Reduction

import Semantics.Clouston.Evaluation.IML
import Semantics.Clouston.Evaluation.IS4

import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.Evaluation.IML
import Semantics.Presheaf.Evaluation.IS4
import Semantics.Presheaf.Necessity

import IS4.Norm
import IS4.Norm.NbE.Model
import IS4.Norm.NbE.Reification
import IS4.Norm.Properties.Completeness
import IS4.Norm.Properties.Soundness

import IS4.Applications.IS4Plus
import IS4.Applications.Purity
