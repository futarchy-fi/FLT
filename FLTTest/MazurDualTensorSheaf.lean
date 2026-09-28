/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ModuleSheafDualSheaf
import FLT.Mazur.ModuleSheafTensorAffineOpen

/-! # Audit of dual sheaves and affine tensor sections

These actual sheaf constructions and comparisons must not acquire arithmetic
assumptions or unfinished proofs through their transitive dependencies.
-/

/-- info: 'FLT.Mazur.FCurve.moduleSheafDual'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleSheafDual

/-- info: 'FLT.Mazur.FCurve.moduleSheafDualMap_comp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleSheafDualMap_comp

/-- info: 'FLT.Mazur.FCurve.moduleSheafDualRestrictIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleSheafDualRestrictIso

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.affineTildeIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.affineTildeIso

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.affineSectionsEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.affineSectionsEquiv

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.affineSectionsEquiv_symm_pure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.affineSectionsEquiv_symm_pure

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.locallyFreeAffineSectionsEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.locallyFreeAffineSectionsEquiv
