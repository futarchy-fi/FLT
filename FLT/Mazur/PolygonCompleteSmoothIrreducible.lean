/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClassifiedFibers
public import FLT.Mazur.SmoothCurveIrreducible

/-!
# Irreducibility of the original nonzero-parameter field squares

The original classification supplies connectedness, and the retained parameter
supplies smooth relative dimension one. Their combination proves irreducibility
of the actual square, rather than requiring it as an additional input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

include ha hs

/-- The actual original field square is irreducible when its parameter is nonzero. -/
theorem completeCartesianField_irreducible : IrreducibleSpace Y := by
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ := (completeCartesianField_classified K n h L _ p q hs).connected
  exact smoothCurve_irreducible q

/-- Reducedness and the constructed irreducibility make the original smooth fiber integral. -/
theorem completeCartesianField_integral : IsIntegral Y := by
  let _ := completeCartesianField_irreducible K n h L a ha p q hs
  let _ := (completeCartesianField_classified K n h L _ p q hs).reduced
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

end FLT.Mazur.PolygonInfinitesimalStages
