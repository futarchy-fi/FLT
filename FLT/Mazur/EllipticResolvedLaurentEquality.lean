/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedLaurentEquality
public import FLT.Mazur.EllipticResolvedSmoothPoint

/-!
# Laurent equality in the actual resolved smooth fiber

The retained-coordinate comparisons specialize to the coefficient data
constructed from the split-depth hypotheses. Thus the actual smooth-fiber
point has the same oriented Laurent equality tests, without extra smoothness data.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Equality of proper specializations is invariant under equality of the stage index. -/
theorem finitePointSpecialization_eq_index_iff
    {K : Type u} [Field K] (A : ValuationSubring K)
    {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
    (data : (i : Fin (n + 1)) → Data W π (start + i.val))
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (he : i = j)
    (P Q : (W.map (algebraMap A K)).toProjective.Point) :
    (finitePointSpecialization A hπ data i hi P =
      finitePointSpecialization A hπ data i hi Q) ↔
        (finitePointSpecialization A hπ data j hj P =
          finitePointSpecialization A hπ data j hj Q) := by
  subst j
  rfl

variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
  (P Q : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = j)
  (w : NodePointCoordinates A W π Q) (hw : w.depth = j)
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D
local notation "r" => depth / 2 - (j + 1)

include hj0 hj hv hw

/-- On a retained depth, the actual smooth points agree exactly at equal primitive residues. -/
theorem resolvedSplitSmoothPoint_retained_eq_iff :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      residue A v.a = residue A w.a ∧ residue A v.b = residue A w.b := by
  rw [resolvedSplitSmoothPoint_eq_iff]
  have h := finitePointSpecialization_retained_eq_iff A hπ data D j (by omega)
    r (by omega) (by omega) (by omega) P Q v (by simpa only [zero_add] using hv)
    w (by simpa only [zero_add] using hw)
  exact (finitePointSpecialization_eq_index_iff A hπ data (j + 1 + r) (depth / 2)
    (by omega) (le_refl _) (by omega) P Q).symm.trans h

/-- The actual negative-branch smooth points are determined by their Laurent characters. -/
theorem resolvedSplitSmoothPoint_negative_eq_iff (hvunit : IsUnit v.b) (hwunit : IsUnit w.b) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      residue A v.b = residue A w.b := by
  rw [resolvedSplitSmoothPoint_eq_iff]
  have h := finitePointSpecialization_retained_negative_eq_iff A hπ data D j (by omega)
    r (by omega) (by omega) (by omega) P Q v (by simpa only [zero_add] using hv)
    w (by simpa only [zero_add] using hw) hvunit hwunit
  exact (finitePointSpecialization_eq_index_iff A hπ data (j + 1 + r) (depth / 2)
    (by omega) (le_refl _) (by omega) P Q).symm.trans h

/-- The actual positive-branch smooth points retain the opposite tangent character. -/
theorem resolvedSplitSmoothPoint_positive_eq_iff
    (hvzero : v.b ∈ maximalIdeal A) (hwzero : w.b ∈ maximalIdeal A) :
    resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q ↔
      residue A (v.b + W.a₁ * v.a) = residue A (w.b + W.a₁ * w.a) := by
  rw [resolvedSplitSmoothPoint_eq_iff]
  have h := finitePointSpecialization_retained_positive_eq_iff A hπ data D j (by omega)
    r (by omega) (by omega) (by omega) P Q v (by simpa only [zero_add] using hv)
    w (by simpa only [zero_add] using hw) hvzero hwzero
  exact (finitePointSpecialization_eq_index_iff A hπ data (j + 1 + r) (depth / 2)
    (by omega) (le_refl _) (by omega) P Q).symm.trans h

/-- Opposite branches at the same retained depth remain distinct in the actual smooth fiber. -/
theorem resolvedSplitSmoothPoint_ne_of_opposite
    (hvunit : IsUnit v.b) (hwzero : w.b ∈ maximalIdeal A) :
    resolvedSplitSmoothPoint A D P ≠ resolvedSplitSmoothPoint A D Q := by
  intro he
  have hb := ((resolvedSplitSmoothPoint_retained_eq_iff A D j hj0 hj P Q v hv w hw).mp he).2
  have hz : residue A w.b = 0 := (residue_eq_zero_iff _).mpr hwzero
  exact (hvunit.map (residue A)).ne_zero (hb.trans hz)

end FLT.Mazur.WeierstrassDividedDepth
