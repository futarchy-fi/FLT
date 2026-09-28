/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ModuleCohomologyExact
import FLT.Mazur.LocalizationCech
import FLT.Mazur.DivisorLineBundleRestrict

/-! # Axiom audit for cohomology and divisor restriction

The geometric foundations must not depend on the unfinished arithmetic inputs.
The Cech checks cover the initial term and the local criterion, not an assertion
of exactness in all degrees.
-/

/-- info: 'FLT.Mazur.FCurve.moduleScalarHConnecting'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarHConnecting

/-- info: 'FLT.Mazur.FCurve.moduleScalarHLongSequence_exact'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarHLongSequence_exact

/-- info: 'FLT.Mazur.FCurve.moduleScalarH_finite_middle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarH_finite_middle

/-- info: 'FLT.Mazur.FCurve.moduleScalarH_finite_right'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarH_finite_right

/-- info: 'FLT.Mazur.FCurve.moduleScalarH_finite_left_succ'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarH_finite_left_succ

/-- info: 'FLT.Mazur.FCurve.moduleScalarH_finite_left_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarH_finite_left_zero

/-- info: 'FLT.Mazur.LocalizationCech.augmentedComplex_exactAt_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCech.augmentedComplex_exactAt_zero

/-- info: 'FLT.Mazur.LocalizationCech.exactAt_iff_sections'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCech.exactAt_iff_sections

/-- info: 'FLT.Mazur.FCurve.EffectiveCartier.divisorLineBundle_locallyFreeRankOne'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.EffectiveCartier.divisorLineBundle_locallyFreeRankOne

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleTopIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleTopIso

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleRestrictIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleRestrictIso

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleRestrictIso_chartTransport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleRestrictIso_chartTransport

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleRestrictLEIso_id'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleRestrictLEIso_id

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleRestrictLEIso_comp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleRestrictLEIso_comp
