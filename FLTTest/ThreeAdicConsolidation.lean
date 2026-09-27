/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.GroupScheme.RaynaudExtension
import FLT.GroupScheme.IntegralEtaleModel
import FLT.GaloisRepresentation.HardlyRamified.KummerTwoDyadic
import FLT.GaloisRepresentation.HardlyRamified.CharacterSeparation
import FLT.GaloisRepresentation.HardlyRamified.RibetAdapters

/-! # Axiom checks for the consolidated three-adic ingredients

These intermediate results must remain independent of the admitted endpoints.
-/

/-- info: 'ThreeAdicPlan.raynaud_extend_generic_morphism_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeAdicPlan.raynaud_extend_generic_morphism_unique

/-- info: 'ThreeAdicPlan.FiniteContinuousGaloisModule.integralEtaleModel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeAdicPlan.FiniteContinuousGaloisModule.integralEtaleModel

/-- info: 'ThreeAdicPlan.no_quadratic_extension_auxiliary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeAdicPlan.no_quadratic_extension_auxiliary

/-- info: 'ThreeAdicPlan.character_eq_one_or_of_each_power_quotient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeAdicPlan.character_eq_one_or_of_each_power_quotient

/-- info: 'StableLattice.isExtensionOf_of_trivial_quotient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms StableLattice.isExtensionOf_of_trivial_quotient
