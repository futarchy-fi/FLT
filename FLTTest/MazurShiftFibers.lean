/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.CechDimensionShift
import FLT.Mazur.DRFiberClassification

/-! # Axiom audit of dimension shifting and classified fiber base change

Degree one is a quotient, not a shifted H0 isomorphism. Fiber classification
is an explicit hypothesis, and the genus condition is still separate.
-/

/-- info: 'FLT.Mazur.CechDimensionShift.cechShiftEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.cechShiftEquiv

/-- info: 'FLT.Mazur.CechDimensionShift.cechShiftEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.cechShiftEquiv_naturality

/-- info: 'FLT.Mazur.CechDimensionShift.cechOneEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.cechOneEquiv

/-- info: 'FLT.Mazur.CechDimensionShift.cechOneEquiv_mk'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.cechOneEquiv_mk

/-- info: 'FLT.Mazur.CechDimensionShift.sheafShiftEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.sheafShiftEquiv

/-- info: 'FLT.Mazur.CechDimensionShift.sheafShiftEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.sheafShiftEquiv_naturality

/-- info: 'FLT.Mazur.CechDimensionShift.sheafOneEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.sheafOneEquiv

/-- info: 'FLT.Mazur.CechDimensionShift.sheafOneEquiv_mk'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechDimensionShift.sheafOneEquiv_mk

/-- info: 'FLT.Mazur.FCurve.DRFiberClassification.ClassifiedGeometricFibers.toNodalGeometricFibers'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.DRFiberClassification.ClassifiedGeometricFibers.toNodalGeometricFibers

/-- info: 'FLT.Mazur.FCurve.DRFiberClassification.ClassifiedGeometricFibers.pullback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.DRFiberClassification.ClassifiedGeometricFibers.pullback

/-- info: 'FLT.Mazur.FCurve.DRFiberClassification.ClassifiedGeometricFibers.baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.DRFiberClassification.ClassifiedGeometricFibers.baseChange

/-- info: 'FLT.Mazur.FCurve.DRFiberClassification.ClassifiedFamilyCore.baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.DRFiberClassification.ClassifiedFamilyCore.baseChange
