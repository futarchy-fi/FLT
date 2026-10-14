/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedTrivializedGeometry
public import FLT.Mazur.EllipticRetainedLaurentCover
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Full geometric images of the retained arithmetic charts

Scaling and inversion preserve the entire retained punctures. Consequently
these arithmetic charts cover the retained tensor open and remain disjoint,
without assuming that geometric residue points lift to generic points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  (j : ℕ) (hj : j + 1 ≤ n) (t : ℕ) (ht : j + 1 + t ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
local notation "F" => ResidueField A
local notation "pos" => retainedTrivializedPositiveChart A hπ data D r j hj t ht hk0 hp
local notation "neg" => retainedTrivializedNegativeChart A hπ data D r j hj t ht hk0 hp

/-- Positive arithmetic scaling preserves the whole retained positive puncture. -/
theorem retainedTrivializedPositiveChart_range :
    Set.range pos = Set.range (retainedPositiveLaurentChart A hπ data D j hj t ht hk0 hp) := by
  rw [retainedTrivializedPositiveChart]
  exact SchemeOpenChartRange.range_iso_comp (asIso (Spec.map (CommRingCat.ofHom
    (PolygonScaledReciprocal.scaling (nodeLaurentScale D r (start + j))).toRingHom))) _

/-- Negative arithmetic inversion preserves the whole retained negative puncture. -/
theorem retainedTrivializedNegativeChart_range :
    Set.range neg = Set.range (retainedNegativeLaurentChart A hπ data D j hj t ht hk0 hp) := by
  rw [retainedTrivializedNegativeChart]
  exact SchemeOpenChartRange.range_iso_comp (asIso (Spec.map (CommRingCat.ofHom
    (PolygonScaledReciprocal.reciprocal (-nodeLaurentScale D r (start + j))).toRingHom))) _

/-- The two arithmetic coordinates cover every geometric point of the retained tensor open. -/
theorem retainedTrivializedCharts_cover :
    Set.range neg ∪ Set.range pos =
      Set.range (finiteRetainedBoundaryTensorChart A hπ data j hj t ht F) := by
  rw [retainedTrivializedPositiveChart_range, retainedTrivializedNegativeChart_range]
  exact retainedLaurentCharts_cover A hπ data D j hj t ht hk0 hp

/-- The arithmetic reparametrizations do not identify the retained punctures. -/
theorem retainedTrivializedCharts_disjoint : Disjoint (Set.range neg) (Set.range pos) := by
  rw [retainedTrivializedPositiveChart_range, retainedTrivializedNegativeChart_range]
  exact retainedLaurentCharts_disjoint A hπ data D j hj t ht hk0 hp

end FLT.Mazur.WeierstrassDividedDepth
