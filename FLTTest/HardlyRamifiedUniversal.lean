/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Deformations.HardlyRamifiedUniversal

/-! # Axiom audit of unrestricted residual universal deformations -/

/-- info: 'Deformation.hardlyRamified_residual_absIrred'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Deformation.hardlyRamified_residual_absIrred

/-- info: 'Deformation.hardlyRamified_exists_universalTraceLift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Deformation.hardlyRamified_exists_universalTraceLift

/-- info: 'Deformation.hardlyRamified_isCorepresentable_deformationFunctor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Deformation.hardlyRamified_isCorepresentable_deformationFunctor
