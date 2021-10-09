module Everything where

import Context

import IK.Substitution
import IK.Conversion
import IK.HellOfSyntacticLemmas
import IK.Norm
import IK.Reduction
import IK.Term
import IK.Type

import IK.Applications.Experiments
import IK.Applications.Neutrality
import IK.Applications.WeakNorm

import IK.Soundness.Presheaf
import IK.Soundness.HellOfSemanticLemmas
import IK.Soundness.Soundness

import IK.Completeness.Trace
import IK.Completeness.Completeness

import IS4.Term
import IS4.Term.Conversion
import IS4.Term.NormalForm
import IS4.Term.Reduction

import IS4.NbE
import IS4.NbE.Model
import IS4.NbE.Reification

import IS4.Norm

import IS4.Applications.Metalanguage
--import IS4.Applications.Purity
import IS4.Applications.Staged

import Semantics.Clouston.Evaluation.IML
import Semantics.Clouston.Evaluation.IS4

import Semantics.Presheaf.Base
import Semantics.Presheaf.CartesianClosure
import Semantics.Presheaf.Evaluation.IML
import Semantics.Presheaf.Evaluation.IS4
import Semantics.Presheaf.Necessity
