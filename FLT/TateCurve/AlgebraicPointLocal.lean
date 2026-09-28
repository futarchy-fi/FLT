/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.AlgebraicUniformization

/-!
# Comparing algebraic and local Tate points

The finite-stage construction agrees with the convergent coordinate series whenever
the ambient algebraic extension is itself a compatible local field.
-/

@[expose] public section

open ValuativeRel
open scoped WeierstrassCurve.Affine TateCurve.FiniteStages

namespace TateCurve.FiniteStages

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsAlgebraic K L] [DecidableEq L]

/-- Over a local algebraic extension, the glued point equals the convergent Tate point. -/
theorem algebraicPoint_eq_uniformizationPointOver (q : Kˣ)
    (hq : valuation K (q : K) < 1) (hL : Continuous (algebraMap K L)) (u : Lˣ) :
    algebraicPoint q hq u = uniformizationPointOver L q hq u := by
  classical
  obtain ⟨M, hM, v, hv⟩ := exists_finite_unit (K := K) u
  let := hM
  rw [← hv, algebraicPoint_map]
  exact map_uniformizationPointOver M.val
    (continuous_algHom_of_finite M.val (continuous_algebraMap M)
      hL) q hq v

end TateCurve.FiniteStages
