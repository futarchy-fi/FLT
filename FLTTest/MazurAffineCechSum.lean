/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.AffineCoherent
import FLT.Mazur.DivisorLineBundleSum
import FLT.Mazur.LocalizationCechCompare
import FLT.Mazur.LocalizationCechSplit
import FLT.Mazur.CechSheafH

/-! # Axiom audit of affine finiteness, Cech comparisons and divisor sums

The split-cover contraction requires a unit member. The degree-zero comparison
does not assert agreement of Cech and Ext cohomology in higher degrees.
-/

/-- info: 'FLT.Mazur.FCurve.affineCoherent_iff_finite_sections'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.affineCoherent_iff_finite_sections

/-- info: 'FLT.Mazur.FCurve.affineCoherent_iff_exists_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.affineCoherent_iff_exists_finite

/-- info: 'FLT.Mazur.FCurve.affineCoherentIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.affineCoherentIso

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleSumIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleSumIso

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleSumIso_eval'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleSumIso_eval

/-- info: 'FLT.Mazur.LocalizationCechCompare.complexIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCechCompare.complexIso

/-- info: 'FLT.Mazur.LocalizationCechCompare.compare_augment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCechCompare.compare_augment

/-- info: 'FLT.Mazur.LocalizationCechCompare.compare_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCechCompare.compare_naturality

/-- info: 'FLT.Mazur.LocalizationCech.split_augmented_exactAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCech.split_augmented_exactAt

/-- info: 'FLT.Mazur.LocalizationCech.split_isZero_homology'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCech.split_isZero_homology

/-- info: 'FLT.Mazur.LocalizationCech.splitHomologyZeroIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCech.splitHomologyZeroIso

/-- info: 'FLT.Mazur.CechSheafH.hZeroEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechSheafH.hZeroEquiv

/-- info: 'FLT.Mazur.CechSheafH.hZeroEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechSheafH.hZeroEquiv_naturality

/-- info: 'FLT.Mazur.FCurve.moduleCechHZeroEquiv_multiply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.moduleCechHZeroEquiv_multiply
