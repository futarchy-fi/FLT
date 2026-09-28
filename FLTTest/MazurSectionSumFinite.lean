/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.SectionSumFinite

/-! # Axiom checks for finiteness of section sums

Finiteness and flatness of these actual closed subschemes require no arithmetic axioms.
-/

/-- info: 'FLT.Mazur.FCurve.finite_fibers_section_prod'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.finite_fibers_section_prod

/-- info: 'FLT.Mazur.FCurve.isFinite_section_prod'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.isFinite_section_prod

/-- info: 'FLT.Mazur.FCurve.finite_flat_smoothOpen_section_prod'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.finite_flat_smoothOpen_section_prod
