/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ModuleSheafDual
import FLT.Mazur.ModuleSheafTensorAffine

/-! # Audit of the dual presheaf and basic-open tensor comparison

These constructions must not depend on arithmetic assumptions. The tensor
comparison targets the tilde of the global tensor; invertibility of its map
to the sheaf tensor remains a separate theorem.
-/

/-- info: 'FLT.Mazur.FCurve.moduleDualPresheaf'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleDualPresheaf

/-- info: 'FLT.Mazur.FCurve.moduleDualRestrict_comp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleDualRestrict_comp

/-- info: 'FLT.Mazur.FCurve.moduleDualRestrict_smul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleDualRestrict_smul

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.basicTensorLinearEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.basicTensorLinearEquiv

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.basicTensorEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.basicTensorEquiv_naturality

/-- info: 'FLT.Mazur.FCurve.ModuleSheafTensor.affineTildeComparison_basicTensorEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.ModuleSheafTensor.affineTildeComparison_basicTensorEquiv
