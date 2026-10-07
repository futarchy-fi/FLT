/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityPairSection
public import FLT.Mazur.WeierstrassProjectiveAdditionChart

/-!
# Residue-field boundary points of input products

On the Y-chart a point with Z = 0 is infinity. Thus a mixed boundary pair
lies in the polynomial output-Z open, while a pair with both Z coordinates
zero factors through the constructed regular infinity addition neighborhood.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R)

/-- Over a field, the boundary of the Y-chart consists of the infinity point. -/
theorem chart_hom_eq_infinity_of_z_eq_zero (f : Coordinate W 1 →ₐ[R] K)
    (hz : f (coord W 1 2) = 0) : f = chartInfinityEvaluation W := by
  have hx := Projective.X_eq_zero_of_Z_eq_zero (projective_equation_of_hom W 1 f) hz
  apply hom_ext
  intro i
  rw [chartInfinityEvaluation_coord]
  fin_cases i
  · exact hx
  · change f (coord W 1 1) = 1
    rw [coord_self, map_one]
  · exact hz

/-- At a left boundary point the polynomial law is the right input scaled by Z. -/
theorem product_add_left_boundary (k : Fin 3) (f : ChartProduct W 1 k →ₐ[R] K)
    (hz : f (chartProductLeft W 1 k (coord W 1 2)) = 0) :
    f ∘ chartProductAdditionCoordinates W 1 k =
      f (chartProductRight W 1 k (coord W k 2)) •
        (f ∘ chartProductRight W 1 k ∘ coord W k) := by
  rw [chartProductAdditionCoordinates_map]
  have he : f ∘ chartProductLeft W 1 k ∘ coord W 1 = ![0, 1, 0] := by
    funext i
    exact (DFunLike.congr_fun
      (chart_hom_eq_infinity_of_z_eq_zero W (f.comp (chartProductLeft W 1 k)) hz)
      (coord W 1 i)).trans (chartInfinityEvaluation_coord W i)
  rw [he]
  exact projectiveAdd_at_left_infinity _ _

/-- At a right boundary point the law is the left input scaled by minus Z. -/
theorem product_add_right_boundary (j : Fin 3) (f : ChartProduct W j 1 →ₐ[R] K)
    (hz : f (chartProductRight W j 1 (coord W 1 2)) = 0) :
    f ∘ chartProductAdditionCoordinates W j 1 =
      -f (chartProductLeft W j 1 (coord W j 2)) •
        (f ∘ chartProductLeft W j 1 ∘ coord W j) := by
  rw [chartProductAdditionCoordinates_map]
  have he : f ∘ chartProductRight W j 1 ∘ coord W 1 = ![0, 1, 0] := by
    funext i
    exact (DFunLike.congr_fun
      (chart_hom_eq_infinity_of_z_eq_zero W (f.comp (chartProductRight W j 1)) hz)
      (coord W 1 i)).trans (chartInfinityEvaluation_coord W i)
  rw [he]
  exact projectiveAdd_at_right_infinity _ _

/-- A mixed left-infinity pair lies in the polynomial output-Z open. -/
theorem product_add_left_boundary_z_ne_zero (k : Fin 3)
    (f : ChartProduct W 1 k →ₐ[R] K)
    (hl : f (chartProductLeft W 1 k (coord W 1 2)) = 0)
    (hr : f (chartProductRight W 1 k (coord W k 2)) ≠ 0) :
    f (chartProductAdditionCoordinates W 1 k 2) ≠ 0 := by
  have h := congrFun (product_add_left_boundary W k f hl) 2
  exact h.trans_ne (mul_ne_zero hr hr)

/-- The opposite mixed pair also lies in the polynomial output-Z open. -/
theorem product_add_right_boundary_z_ne_zero (j : Fin 3)
    (f : ChartProduct W j 1 →ₐ[R] K)
    (hl : f (chartProductLeft W j 1 (coord W j 2)) ≠ 0)
    (hr : f (chartProductRight W j 1 (coord W 1 2)) = 0) :
    f (chartProductAdditionCoordinates W j 1 2) ≠ 0 := by
  have h := congrFun (product_add_right_boundary W j f hr) 2
  exact h.trans_ne (mul_ne_zero (neg_ne_zero.mpr hl) hl)

/-- A pair on both boundaries is the base change of the integral infinity-pair section. -/
theorem product_boundary_pair_eq (f : ChartProduct W 1 1 →ₐ[R] K)
    (hl : f (chartProductLeft W 1 1 (coord W 1 2)) = 0)
    (hr : f (chartProductRight W 1 1 (coord W 1 2)) = 0) :
    f = (Algebra.ofId R K).comp (infinityPairEvaluation W) := by
  apply chartProduct_hom_ext
  · apply hom_ext
    intro i
    have h := DFunLike.congr_fun
      (chart_hom_eq_infinity_of_z_eq_zero W (f.comp (chartProductLeft W 1 1)) hl)
      (coord W 1 i)
    change _ = algebraMap R K (infinityLeft W (infinityPairEvaluation W) i)
    rw [infinityPairEvaluation_left]
    rw [chartInfinityEvaluation_coord] at h
    exact h.trans (by fin_cases i <;> simp)
  · apply hom_ext
    intro i
    have h := DFunLike.congr_fun
      (chart_hom_eq_infinity_of_z_eq_zero W (f.comp (chartProductRight W 1 1)) hr)
      (coord W 1 i)
    change _ = algebraMap R K (infinityRight W (infinityPairEvaluation W) i)
    rw [infinityPairEvaluation_right]
    rw [chartInfinityEvaluation_coord] at h
    exact h.trans (by fin_cases i <;> simp)

/-- The boundary pair factors through the actual two-stage infinity addition domain. -/
theorem product_boundary_pair_lift (f : ChartProduct W 1 1 →ₐ[R] K)
    (hl : f (chartProductLeft W 1 1 (coord W 1 2)) = 0)
    (hr : f (chartProductRight W 1 1 (coord W 1 2)) = 0) :
    ∃ g : InfinityAdditionOpen W →ₐ[R] K,
      g.comp (infinityAdditionRestriction W) = f := by
  refine ⟨(Algebra.ofId R K).comp (infinityPairAdditionLift W), ?_⟩
  rw [AlgHom.comp_assoc, infinityPairAdditionLift_restriction,
    ← product_boundary_pair_eq W f hl hr]

end FLT.Mazur.WeierstrassIntegralChart
