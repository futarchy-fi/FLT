/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.CechFreeOpenStalk
import FLT.Mazur.CurveFiberHypotheses
import FLT.Mazur.ProjectiveLineEndpoints

/-! # Axiom audit of stalks, nodal fiber conditions and projective-line endpoints

The fiber conditions are explicitly partial. The projective line and its
distinct endpoints do not yet construct the cyclic polygon quotient.
-/

/-- info: 'FLT.Mazur.CechFreeOpen.freeOpenStalkIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeOpen.freeOpenStalkIso

/-- info: 'FLT.Mazur.CechFreeOpen.freeOpenStalk_isZero_of_notMem'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeOpen.freeOpenStalk_isZero_of_notMem

/-- info: 'FLT.Mazur.CechFreeOpen.freeOpenStalkIso_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeOpen.freeOpenStalkIso_naturality

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmentedStalkIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmentedStalkIso

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmentedStalkι_d'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmentedStalkι_d

/-- info: 'FLT.Mazur.FCurve.CurveNode.isNode_iff_hasNodePresentation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CurveNode.isNode_iff_hasNodePresentation

/-- info: 'FLT.Mazur.FCurve.CurveNode.atWorstNodes_of_smooth'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CurveNode.atWorstNodes_of_smooth

/-- info: 'FLT.Mazur.FCurve.CurveFiberHypotheses.NodalGeometricFibers.baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CurveFiberHypotheses.NodalGeometricFibers.baseChange

/-- info: 'FLT.Mazur.FCurve.CurveFiberHypotheses.NodalFamilyCore.baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CurveFiberHypotheses.NodalFamilyCore.baseChange

/-- info: 'FLT.Mazur.ProjectiveLine.scheme'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveLine.scheme

/-- info: 'FLT.Mazur.ProjectiveLine.charts_cover'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveLine.charts_cover

/-- info: 'FLT.Mazur.ProjectiveLine.zero_toBase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveLine.zero_toBase

/-- info: 'FLT.Mazur.ProjectiveLine.infinity_toBase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveLine.infinity_toBase

/-- info: 'FLT.Mazur.ProjectiveLine.zeroSection_ne_infinitySection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveLine.zeroSection_ne_infinitySection
