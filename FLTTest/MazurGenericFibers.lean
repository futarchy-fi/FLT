/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.Mazur.GenericFibers

/-! # Axiom checks for the generic-point finiteness argument

Geometry, distinct cusp images and finite quotient points are explicit inputs.
These implications must not use Mazur's torsion theorem or the final FLT theorem.
-/

/-- info: 'FLT.Mazur.Points.pullbackEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.Points.pullbackEquiv

/-- info: 'FLT.Mazur.QuotientData.genericProjection_nonconstant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.QuotientData.genericProjection_nonconstant

/-- info: 'FLT.Mazur.QuotientData.g2Fibers'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.QuotientData.g2Fibers

/-- info: 'FLT.Mazur.QuotientData.g2CurveFinite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.QuotientData.g2CurveFinite

/-- info: 'FLT.Mazur.FCurve.topologicalKrullDim_le_one_of_smooth'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.FCurve.topologicalKrullDim_le_one_of_smooth

/-- info: 'FLT.Mazur.IntegralData.generic_dimension_le_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.Mazur.IntegralData.generic_dimension_le_one

-- The geometric input suffices; no additional generic dimension bound is assumed.
example {p : ℕ} (D : FLT.Mazur.IntegralData p) (Q : FLT.Mazur.QuotientData D)
    (hgeometry : FLT.Mazur.G1Geometry D)
    (hc : FLT.Mazur.G2Cusps Q) (hfinite : FLT.Mazur.G2Finite Q)
    [AlgebraicGeometry.IsSeparated Q.A.hom] : FLT.Mazur.G2CurveFinite D :=
  Q.g2CurveFinite hgeometry hc hfinite
