/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBranchSwap
public import FLT.Mazur.LaurentUnitPoints

/-!
# Full node maps on a puncture are determined by its coordinate unit

A unit image of either node coordinate gives the complete Laurent
factorization. The relation determines the opposite coordinate, including
its smoothing coefficient and every nilpotent term.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
set_option backward.isDefEq.respectTransparency false

/-- A full node map whose left coordinate is a unit factors through the entire left puncture. -/
theorem nodeMap_factor_left (s : R) (f : ChartRing s →ₐ[R] A) (u : Aˣ)
    (hu : f (leftCoordinate s) = ↑u) :
    f = (LaurentUnitPoints.evalUnit u).comp (leftLaurentMap s) := by
  apply chartRing_hom_ext s
  · simpa only [AlgHom.comp_apply, leftLaurentMap_left, LaurentUnitPoints.evalUnit_T,
      zpow_one] using hu
  · have hf : (u : A) * f (rightCoordinate s) = algebraMap R A s := by
      rw [← hu, ← map_mul, coordinate_relation, AlgHom.commutes]
    simp only [AlgHom.comp_apply, leftLaurentMap_right, map_mul,
      LaurentUnitPoints.evalUnit_C, LaurentUnitPoints.evalUnit_T, zpow_neg_one]
    calc
      _ = ↑u⁻¹ * ((u : A) * f (rightCoordinate s)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hf, mul_comm]

/-- A full node map whose right coordinate is a unit factors through the entire right puncture. -/
theorem nodeMap_factor_right (s : R) (f : ChartRing s →ₐ[R] A) (u : Aˣ)
    (hu : f (rightCoordinate s) = ↑u) :
    f = (LaurentUnitPoints.evalUnit u).comp
      ((leftLaurentMap s).comp (branchSwapMap s)) := by
  have h := nodeMap_factor_left s (f.comp (branchSwapMap s)) u
    (by simpa only [AlgHom.comp_apply, branchSwapMap_left] using hu)
  have hc := congrArg (fun g : ChartRing s →ₐ[R] A ↦ g.comp (branchSwapMap s)) h
  simpa only [AlgHom.comp_assoc, branchSwapMap_comp, AlgHom.comp_id] using hc

end FLT.Mazur.PolygonSmoothing
