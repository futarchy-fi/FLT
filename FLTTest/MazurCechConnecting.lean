/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.CechConnecting
import FLT.Mazur.CoherentDevissage

/-! # Axiom audit of Cech connecting maps and the coherent induction core

Cover acyclicity and coherent short exact sequences remain explicit hypotheses.
This audit does not assert the full geometric devissage criterion.
-/

/-- info: 'FLT.Mazur.CechConnecting.cechShortComplex_shortExact'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechConnecting.cechShortComplex_shortExact

/-- info: 'FLT.Mazur.CechConnecting.cechDelta'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechConnecting.cechDelta

/-- info: 'FLT.Mazur.CechConnecting.cechDelta_exact'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechConnecting.cechDelta_exact

/-- info: 'FLT.Mazur.CechConnecting.cechDelta_exact_next'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechConnecting.cechDelta_exact_next

/-- info: 'FLT.Mazur.CechConnecting.cechDelta_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechConnecting.cechDelta_naturality

/-- info: 'FLT.Mazur.FCurve.CoherentDevissage.support_subset_of_mono'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CoherentDevissage.support_subset_of_mono

/-- info: 'FLT.Mazur.FCurve.CoherentDevissage.closed_induction_on_irreducible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CoherentDevissage.closed_induction_on_irreducible

/-- info: 'FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.common_subobject'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.common_subobject

/-- info: 'FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.common_quotient'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.common_quotient

/-- info: 'FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.finite_extensions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.finite_extensions

/-- info: 'FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.remaining_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.CoherentDevissage.TwoOutOfThree.remaining_factor
