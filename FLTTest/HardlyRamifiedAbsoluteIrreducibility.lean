/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.GaloisRepresentation.HardlyRamified.AbsoluteIrreducibility

/-! # Axiom audit of residual absolute irreducibility -/

/-- info: 'ThreeAdicPlan.charP_of_finite_padic_algebra'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeAdicPlan.charP_of_finite_padic_algebra

/-- info: 'ThreeAdicPlan.rationalComplexConjugation_mul_self'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThreeAdicPlan.rationalComplexConjugation_mul_self

/-- info: 'LinearMap.finrank_fixed_of_involutive_det_neg_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.finrank_fixed_of_involutive_det_neg_one

/-- info: 'GaloisRepresentation.IsHardlyRamified.complexConjugation_fixed_finrank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaloisRepresentation.IsHardlyRamified.complexConjugation_fixed_finrank

/-- info: 'GaloisRepresentation.IsHardlyRamified.isAbsolutelyIrreducible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaloisRepresentation.IsHardlyRamified.isAbsolutelyIrreducible
