/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.EllipticCurve.CubicAffineInverse
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
