/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineMarkedCharts

/-!
# Powers of the polygon boundary ideal on normalization charts

All positive multiplicities, and the zeroth power, commute with the actual
normalization and affine-chart pullbacks. This concerns ideal sheaves;
identifying pullbacks of their dual modules is a further comparison.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FCurve

/-- Powers of ideal sheaves commute with arbitrary scheme pullback. -/
theorem idealSheaf_comap_pow {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : Y ⟶ X) (m : ℕ) : (I ^ m).comap f = I.comap f ^ m := by
  induction m with
  | zero => simp only [pow_zero, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top]
  | succ m ih => rw [pow_succ, idealSheaf_comap_mul, ih, pow_succ]
end FLT.Mazur.FCurve
namespace FLT.Mazur.PolygonDivisorPowerPullback
open PolygonPinching PolygonDivisorNormalizationPullback FCurve
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- Every divisor power pulls back to the same power of the marked ideal. -/
theorem normalization (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    ((PolygonBoundaryDivisor.ideal K n p a) ^ m).comap (componentι K n i ≫ p).left =
      (markedPoint K (a i)).ker ^ m := by
  rw [idealSheaf_comap_pow, ideal K n hn p q h]
include h in
/-- The left affine chart of a component retains the marked multiplicity. -/
theorem left_chart (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    ((PolygonBoundaryDivisor.ideal K n p a) ^ m).comap
      (ProjectiveLine.left K ≫ (componentι K n i ≫ p).left) =
        (ProjectiveLineMarkedCharts.chartPoint K (a i)).ker ^ m := by
  rw [Scheme.IdealSheafData.comap_comp, normalization K n hn p q h,
    idealSheaf_comap_pow, ProjectiveLineMarkedCharts.left_ideal]
include h in
/-- The right affine chart uses the reciprocal coordinate and the same multiplicity. -/
theorem right_chart (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    ((PolygonBoundaryDivisor.ideal K n p a) ^ m).comap
      (ProjectiveLine.right K ≫ (componentι K n i ≫ p).left) =
        (ProjectiveLineMarkedCharts.chartPoint K ((a i)⁻¹ : Kˣ)).ker ^ m := by
  rw [Scheme.IdealSheafData.comap_comp, normalization K n hn p q h,
    idealSheaf_comap_pow, ProjectiveLineMarkedCharts.right_ideal]
end FLT.Mazur.PolygonDivisorPowerPullback
