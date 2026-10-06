/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.EllipticCurve.CubicIntegralReduction
import FLT.EllipticCurve.CubicTorsionLocalFree
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
