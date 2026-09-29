/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.ClosedSubschemeCohomology
import FLT.Mazur.CoherentAffineCoverSections

/-! # Axiom audit of affine-cover and closed-subscheme cohomology

Covers, quasi-coherence and base-ring finiteness hypotheses are retained.
The conditional finiteness results do not imply general proper finiteness.
-/

namespace FLT.Mazur.CechAcyclicComparison

/-- info: 'FLT.Mazur.CechAcyclicComparison.acyclicCoverEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acyclicCoverEquiv

end FLT.Mazur.CechAcyclicComparison

namespace FLT.Mazur.CechAcyclicNaturality

/-- info: 'FLT.Mazur.CechAcyclicNaturality.acyclicCoverEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acyclicCoverEquiv_naturality

/-- info: 'FLT.Mazur.CechAcyclicNaturality.comparisonFromSequence_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comparisonFromSequence_eq

end FLT.Mazur.CechAcyclicNaturality

namespace FLT.Mazur.FCurve

/-- info: 'FLT.Mazur.FCurve.affine_moduleH_succ_subsingleton'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affine_moduleH_succ_subsingleton

/-- info: 'FLT.Mazur.FCurve.affineCoverCechEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affineCoverCechEquiv

/-- info: 'FLT.Mazur.FCurve.affineCoverCechEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affineCoverCechEquiv_naturality

/-- info: 'FLT.Mazur.FCurve.finiteAffineCover_moduleH_subsingleton'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteAffineCover_moduleH_subsingleton

/-- info: 'FLT.Mazur.FCurve.emptyAffineCover_moduleH_subsingleton'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emptyAffineCover_moduleH_subsingleton

/-- info: 'FLT.Mazur.FCurve.affineCoverModuleH_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms affineCoverModuleH_finite

/-- info: 'FLT.Mazur.FCurve.coherentAffineCover_moduleH_finite_of_sections'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coherentAffineCover_moduleH_finite_of_sections

/-- info: 'FLT.Mazur.FCurve.closedPushforwardModuleHEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closedPushforwardModuleHEquiv

/-- info: 'FLT.Mazur.FCurve.closedPushforwardRingHEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closedPushforwardRingHEquiv

/-- info: 'FLT.Mazur.FCurve.closedSubscheme_moduleH_subsingleton'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closedSubscheme_moduleH_subsingleton

/-- info: 'FLT.Mazur.FCurve.closedPushforward_moduleH_finite_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closedPushforward_moduleH_finite_iff

end FLT.Mazur.FCurve


/-- info: 'FLT.Mazur.PushforwardCech.moduleCechEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.PushforwardCech.moduleCechEquiv_naturality

/-- info: 'FLT.Mazur.FCurve.closedPushforwardCoverHEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.closedPushforwardCoverHEquiv_naturality

/-- info: 'FLT.Mazur.FCurve.closedPushforwardModuleHEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.closedPushforwardModuleHEquiv_naturality

/-- info: 'FLT.Mazur.FCurve.closedPushforwardRingHEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.closedPushforwardRingHEquiv_naturality

/-- info: 'FLT.Mazur.FCurve.closedPushforwardScalarHEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.closedPushforwardScalarHEquiv_naturality
