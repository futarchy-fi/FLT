/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.CechInjectiveAcyclic
import FLT.Mazur.CechAcyclicCokernel

/-! # Axiom audit of the free Cech resolution and injective acyclicity

Exactness includes the integer augmentation. Cover acyclicity remains an
explicit hypothesis when proving short exactness of coefficient Cech terms.
-/

/-- info: 'FLT.Mazur.CechFreeResolution.freeStalkExtraDegeneracy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeStalkExtraDegeneracy

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmented_stalk_exactAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmented_stalk_exactAt

/-- info: 'FLT.Mazur.CechFreeResolution.freeAugmented_exactAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechFreeResolution.freeAugmented_exactAt

/-- info: 'FLT.Mazur.CechInjectiveAcyclic.homTermEquiv_d'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechInjectiveAcyclic.homTermEquiv_d

/-- info: 'FLT.Mazur.CechInjectiveAcyclic.cech_isZero_of_injective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechInjectiveAcyclic.cech_isZero_of_injective

/-- info: 'FLT.Mazur.CechAcyclicCokernel.coverAcyclic_of_injective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechAcyclicCokernel.coverAcyclic_of_injective

/-- info: 'FLT.Mazur.CechAcyclicCokernel.coverAcyclic_cokernel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechAcyclicCokernel.coverAcyclic_cokernel

/-- info: 'FLT.Mazur.CechAcyclicCokernel.sections_surjective_of_hPrime_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechAcyclicCokernel.sections_surjective_of_hPrime_one

/-- info: 'FLT.Mazur.CechAcyclicCokernel.cech_degree_shortExact'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.CechAcyclicCokernel.cech_degree_shortExact
