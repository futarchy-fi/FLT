/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ProjectiveCoherentCohomology

/-! # Axiom audit of coherent projective cohomology finiteness -/

/-- info: 'FLT.Mazur.FCurve.freeSheaf_isFinitePresentation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.freeSheaf_isFinitePresentation

/-- info: 'FLT.Mazur.FCurve.unitSheaf_isFinitePresentation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.unitSheaf_isFinitePresentation

/-- info: 'FLT.Mazur.ProjectiveSpace.twistingSheaf_isFinitePresentation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveSpace.twistingSheaf_isFinitePresentation

/-- info: 'FLT.Mazur.ProjectiveSpace.twistCechHomologyEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveSpace.twistCechHomologyEquiv

/-- info: 'FLT.Mazur.ProjectiveSpace.twistModuleHEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveSpace.twistModuleHEquiv

/-- info: 'FLT.Mazur.ProjectiveSpace.twist_moduleH_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveSpace.twist_moduleH_finite

/-- info: 'FLT.Mazur.FCurve.moduleRingH_finite_coproduct'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleRingH_finite_coproduct

/-- info: 'FLT.Mazur.FCurve.moduleRingH_finite_right'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleRingH_finite_right

/-- info: 'FLT.Mazur.ProjectiveSpace.coherent_moduleH_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveSpace.coherent_moduleH_finite

/-- info: 'FLT.Mazur.ProjectiveSpace.closedSubscheme_coherent_moduleH_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.ProjectiveSpace.closedSubscheme_coherent_moduleH_finite
