/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.CartierTensorRank
import FLT.Mazur.CurveGenus
import FLT.Mazur.DivisorRestrictCoherence

/-! # Axiom audit of the integrated sheaf and degree-zero cohomology constructions -/

/-- info: 'FLT.Mazur.FCurve.CartierChart.dualRestrict_comp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CartierChart.dualRestrict_comp

/-- info: 'FLT.Mazur.FCurve.EffectiveCartier.idealModule_locallyFreeRankOne'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.EffectiveCartier.idealModule_locallyFreeRankOne

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.homEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.homEquiv

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.restrictIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.restrictIso

/-- info: 'FLT.Mazur.FCurve.EffectiveCartier.idealModule_tensor_locallyFreeRankOne'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.EffectiveCartier.idealModule_tensor_locallyFreeRankOne

/-- info: 'FLT.Mazur.FCurve.finrank_H0_of_constantGlobalSections'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.finrank_H0_of_constantGlobalSections
