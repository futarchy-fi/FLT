/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.EllipticCurve.InfinityChart
import Mathlib.Data.ZMod.Basic
import Lean

/-! # Trust audit of the concrete infinity chart -/

open Lean Elab Command CategoryTheory

run_elab do
  for n in #[``WeierstrassCurve.InfinityChart.equation,
      ``WeierstrassCurve.InfinityChart.equation_eq_dehomogenization,
      ``WeierstrassCurve.InfinityChart.scheme,
      ``WeierstrassCurve.InfinityChart.inclusion,
      ``WeierstrassCurve.InfinityChart.inclusion_isClosedImmersion,
      ``WeierstrassCurve.InfinityChart.toBase,
      ``WeierstrassCurve.InfinityChart.origin,
      ``WeierstrassCurve.InfinityChart.infinity,
      ``WeierstrassCurve.InfinityChart.infinity_toBase,
      ``WeierstrassCurve.InfinityChart.derivative_at_origin,
      ``WeierstrassCurve.InfinityChart.transition_equation,
      ``WeierstrassCurve.InfinityChart.point,
      ``WeierstrassCurve.InfinityChart.point_coordinate,
      ``WeierstrassCurve.InfinityChart.hom_ext,
      ``WeierstrassCurve.InfinityChart.existsUnique_point] do
    for a in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected axiom {a} in {n}"

-- The chart and its section also exist over a nonreduced, non-field base.
-- This exercises the geometric construction without field or discriminant hypotheses.
example (W : WeierstrassCurve (ZMod 4)) :
    WeierstrassCurve.InfinityChart.infinity W ≫
      WeierstrassCurve.InfinityChart.toBase W = 𝟙 _ :=
  WeierstrassCurve.InfinityChart.infinity_toBase W
