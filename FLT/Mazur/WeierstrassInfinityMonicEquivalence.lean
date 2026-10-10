/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityCoordinateRegular
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The monic model is the actual infinity chart

Both explicit comparisons are inverse. In particular the existing chart is
free, hence flat, over the original coefficient ring. This gives the base
flatness needed to transport coordinate regularity through product charts.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The comparison also fixes the monic model's two algebra generators. -/
theorem infinityChartToMonic_comp :
    (infinityChartToMonic W).comp (infinityMonicToChart W) =
      AlgHom.id R (InfinityMonicModel W) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change infinityChartToMonic W
      (infinityMonicToChart W (AdjoinRoot.of (infinityMonicPolynomial W) X)) =
        AdjoinRoot.of (infinityMonicPolynomial W) X
    rw [infinityMonicToChart, AdjoinRoot.liftAlgHom_of, aeval_X]
    exact evaluation_coord W 1 _ _ _ 2
  · change infinityChartToMonic W
      (infinityMonicToChart W (AdjoinRoot.root (infinityMonicPolynomial W))) =
        AdjoinRoot.root (infinityMonicPolynomial W)
    rw [infinityMonicToChart, AdjoinRoot.liftAlgHom_root]
    exact evaluation_coord W 1 _ _ _ 0

/-- An explicit coefficient-preserving equivalence with the original quotient chart. -/
def infinityChartMonicEquiv : Coordinate W 1 ≃ₐ[R] InfinityMonicModel W :=
  AlgEquiv.ofAlgHom (infinityChartToMonic W) (infinityMonicToChart W)
    (infinityChartToMonic_comp W) (infinityMonicToChart_comp W)

/-- The original infinity chart is a free module over every base coefficient ring. -/
theorem infinityChart_free : Module.Free R (Coordinate W 1) := by
  let _ := infinityMonicModel_free W
  let _ : Module.Free R (InfinityMonicModel W) := Module.Free.trans (S := R[X])
  exact Module.Free.of_equiv (infinityChartMonicEquiv W).symm.toLinearEquiv

/-- In particular the original infinity chart is flat over its coefficient ring. -/
theorem infinityChart_flat : Module.Flat R (Coordinate W 1) := by
  let _ := infinityChart_free W
  infer_instance

/-- Flat scalar extensions preserve regularity of the actual infinity Z coordinate. -/
theorem infinityChart_coord_z_regular_baseChange {S : Type*} [CommRing S]
    [Algebra (Coordinate W 1) S] [Module.Flat (Coordinate W 1) S] :
    IsRegular (algebraMap (Coordinate W 1) S (coord W 1 2)) := by
  have h := Module.Flat.isSMulRegular_of_isRegular (M := S) (infinityChart_coord_z_regular W)
  have hl : IsLeftRegular (algebraMap (Coordinate W 1) S (coord W 1 2)) := by
    simpa only [IsLeftRegular, IsSMulRegular, Algebra.smul_def] using h
  exact ⟨hl, fun a b he => hl (by simpa only [mul_comm] using he)⟩

end FLT.Mazur.WeierstrassIntegralChart
