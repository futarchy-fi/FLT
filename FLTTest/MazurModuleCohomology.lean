/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ModuleCohomology

/-! # Audit of module-coefficient cohomology and its canonical comparisons -/

/-- info: 'FLT.Mazur.FCurve.moduleScalarHFunctor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarHFunctor

/-- info: 'FLT.Mazur.FCurve.moduleScalarHUnitEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarHUnitEquiv

/-- info: 'FLT.Mazur.FCurve.moduleScalarH0Equiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarH0Equiv

/-- info: 'FLT.Mazur.FCurve.moduleScalarHMap_comp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarHMap_comp

/-- info: 'FLT.Mazur.FCurve.moduleScalarH0Equiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleScalarH0Equiv_naturality
