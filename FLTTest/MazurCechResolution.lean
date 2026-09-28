/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.LocalizationCechExact
import FLT.Mazur.CechFreeResolution
import FLT.Mazur.DivisorLineBundleSumUnit

/-! # Axiom audit for Cech foundations and divisor units

Exactness of principal-open section complexes is distinguished from the
construction of the augmented free-sheaf complex and the H0 comparison.
-/

/-- info: 'FLT.Mazur.LocalizationCechExact.augmented_exactAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCechExact.augmented_exactAt

/-- info: 'FLT.Mazur.LocalizationCechExact.isZero_homology'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCechExact.isZero_homology

/-- info: 'FLT.Mazur.LocalizationCechExact.homologyZeroIso_augmentation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.LocalizationCechExact.homologyZeroIso_augmentation

/-- info: 'FLT.Mazur.CechSheafHZero.sheafHZeroEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechSheafHZero.sheafHZeroEquiv

/-- info: 'FLT.Mazur.CechSheafHZero.sheafHZeroEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechSheafHZero.sheafHZeroEquiv_naturality

/-- info: 'FLT.Mazur.CechFreeOpen.freeOpenHomEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeOpen.freeOpenHomEquiv

/-- info: 'FLT.Mazur.CechFreeOpen.hPrimeZeroEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeOpen.hPrimeZeroEquiv_naturality

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmented'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmented

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmentedTermIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmentedTermIso

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmentedι_d'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmentedι_d

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmentedι_augmentation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmentedι_augmentation

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleSumIso_leftUnit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleSumIso_leftUnit

/-- info: 'FLT.Mazur.FCurve.divisorLineBundleSumIso_rightUnit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.divisorLineBundleSumIso_rightUnit
