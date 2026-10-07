/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.EllipticCurve.CubicIntegralReduction
import FLT.EllipticCurve.CubicGoodReduction
import FLT.EllipticCurve.CubicLegendre
import FLT.EllipticCurve.CubicBaseChangeAddition
import FLT.EllipticCurve.CubicBaseChangeGroup
import FLT.EllipticCurve.CubicBaseChangeTorsion
import FLT.EllipticCurve.CubicLegendreJFinite
import FLT.EllipticCurve.CubicLegendreMonic
import FLT.EllipticCurve.CubicLegendreParameters
import FLT.EllipticCurve.CubicLevelParameters
import FLT.EllipticCurve.CubicTorsionQuotient
import FLT.EllipticCurve.CubicCyclicSpecialization
import FLT.EllipticCurve.CubicCyclicDedekind
import FLT.EllipticCurve.CubicCyclicEtaleField
import FLT.EllipticCurve.CubicCyclicNaturality
import FLT.EllipticCurve.CubicCyclicGaloisDescent
import FLT.EllipticCurve.CubicUniversalCyclicParameters
import FLT.EllipticCurve.CubicPrimeCyclicDegree
import FLT.EllipticCurve.CubicPrimeCyclicSubgroups
import FLT.EllipticCurve.CubicTorsionQuotientPoints
import FLT.EllipticCurve.CubicTorsionFlat
import FLT.EllipticCurve.CubicTorsionEtaleAlgebra
import FLT.EllipticCurve.CubicTorsionEtaleFibers
import FLT.EllipticCurve.CubicAffineInverse
import FLT.EllipticCurve.CubicInfinityChartAddition
import FLT.EllipticCurve.CubicInfinityFiniteComparison
import FLT.EllipticCurve.CubicInfinityComparison
import FLT.EllipticCurve.CubicInfinityRegular
import FLT.EllipticCurve.CubicMixedOpposite
import FLT.EllipticCurve.CubicMixedRegular
import FLT.EllipticCurve.CubicMixedProjective
import Mathlib.Data.ZMod.Basic
import FLT.EllipticCurve.CubicCyclicIncidence
import FLT.EllipticCurve.CubicCyclicIncidencePoints
import FLT.EllipticCurve.CubicCyclicParameterTransport
import FLT.EllipticCurve.CubicCyclicTransportFunctor
import FLT.EllipticCurve.CubicScalarDescent
import FLT.EllipticCurve.CubicCyclicGroup
import FLT.EllipticCurve.CubicCyclicEmbedding
import FLT.EllipticCurve.CubicInvariantTrace
import FLT.EllipticCurve.CubicCyclicEtale
import FLT.EllipticCurve.CubicUniversalCyclicGroup
import FLT.EllipticCurve.CubicVariableChange
import FLT.EllipticCurve.CubicVariableChangeGlobal
import FLT.EllipticCurve.CubicVariableChangeIso
import FLT.EllipticCurve.CubicVariableChangeGroup
import FLT.EllipticCurve.CubicTorsionTransport
import FLT.EllipticCurve.CubicNonzeroScalarTransport
import FLT.EllipticCurve.CubicNonzeroTransport
import FLT.EllipticCurve.CubicInvariantTransport
import FLT.EllipticCurve.CubicVariableChangeOverlap
import Lean

/-! # Trust audit of both chart transitions and the glued scheme -/

open Lean Elab Command CategoryTheory

run_elab do
  let auditedNamespace := `WeierstrassCurve.CubicCharts
  let mut count := 0
  for (n, _) in (← getEnv).constants.toList do
    if auditedNamespace.isPrefixOf n then
      count := count + 1
      for a in ← Lean.collectAxioms n do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "Unexpected axiom {a} in {n}"
  if count == 0 then
    throwError "No cubic-chart declarations were audited"

-- The geometric gluing works over nonreduced coefficient rings.
example (W : WeierstrassCurve (ZMod 4)) :
    WeierstrassCurve.CubicCharts.infinity W ≫
      WeierstrassCurve.CubicCharts.toBase W = 𝟙 _ :=
  WeierstrassCurve.CubicCharts.infinity_toBase W

-- The actual overlap algebra equivalence works in characteristic three.
example (W : WeierstrassCurve (ZMod 3))
    (x : WeierstrassCurve.CubicCharts.Overlap W false) :
    (WeierstrassCurve.CubicCharts.overlapEquiv W).symm
      (WeierstrassCurve.CubicCharts.overlapEquiv W x) = x :=
  (WeierstrassCurve.CubicCharts.overlapEquiv W).symm_apply_apply x

-- Finiteness also covers torsion whose order is the residue characteristic.
example (W : WeierstrassCurve (ZMod 2)) [W.IsElliptic] :
    AlgebraicGeometry.IsFinite
      (WeierstrassCurve.CubicCharts.torsionModel W 2).hom :=
  WeierstrassCurve.CubicCharts.torsionModel_finite W (by decide)

open scoped TensorProduct in
-- Prime-to-characteristic torsion has an étale coordinate fiber.
example (W : WeierstrassCurve (ZMod 2)) [W.IsElliptic] :
    Algebra.Etale (ZMod 2)
      ((ZMod 2) ⊗[ZMod 2] WeierstrassCurve.CubicCharts.torsionCoordinateRing W 3) :=
  WeierstrassCurve.CubicCharts.torsionCoordinate_field_etale W 3 (ZMod 2) (by decide)
