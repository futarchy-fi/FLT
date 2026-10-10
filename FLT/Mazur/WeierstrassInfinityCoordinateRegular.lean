/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityMonicPolynomial
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The infinity chart's Z coordinate is regular over every base ring

An explicit retraction embeds the existing chart quotient in the free monic
model over R[Z]. Multiplication by Z is injective there, hence also on the
original chart. This is a ring-level statement and does not discard nilpotents.
-/

@[expose] public noncomputable section

open Polynomial WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Send the original normalized coordinates to the monic model's X and Z. -/
def infinityChartToMonic : Coordinate W 1 →ₐ[R] InfinityMonicModel W :=
  evaluation W 1 ![AdjoinRoot.root (infinityMonicPolynomial W), 1,
    algebraMap R[X] (InfinityMonicModel W) X] (infinityMonicModel_equation W) rfl

/-- The original chart's coordinates satisfy the monic presentation relation. -/
theorem infinityMonicPolynomial_chart_root :
    (infinityMonicPolynomial W).eval₂ (aeval (coord W 1 2)).toRingHom (coord W 1 0) = 0 := by
  rw [infinityMonicPolynomial_eval]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X]
  have h := coord_equation W 1
  rw [Projective.equation_iff] at h
  simp only [coord_self, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  linear_combination -h

/-- Evaluate the monic model back in the original quotient. -/
def infinityMonicToChart : InfinityMonicModel W →ₐ[R] Coordinate W 1 :=
  AdjoinRoot.liftAlgHom (infinityMonicPolynomial W) (aeval (coord W 1 2))
    (coord W 1 0) (infinityMonicPolynomial_chart_root W)

/-- The monic-model comparison is a retraction on the original chart. -/
theorem infinityMonicToChart_comp :
    (infinityMonicToChart W).comp (infinityChartToMonic W) = AlgHom.id R (Coordinate W 1) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp [infinityChartToMonic, infinityMonicToChart, AdjoinRoot.algebraMap_eq, coord_self,
      AdjoinRoot.liftAlgHom_root, AdjoinRoot.liftAlgHom_of]

/-- In particular the coordinate comparison loses no elements of the original chart. -/
theorem infinityChartToMonic_injective : Function.Injective (infinityChartToMonic W) := by
  intro a b h
  have he := congrArg (infinityMonicToChart W) h
  simpa only [← AlgHom.comp_apply, infinityMonicToChart_comp, AlgHom.id_apply] using he

/-- Multiplication by the actual Z coordinate is injective on the infinity chart. -/
theorem infinityChart_coord_z_regular : IsRegular (coord W 1 2) := by
  let _ := infinityMonicModel_free W
  have hZ := Module.Flat.isSMulRegular_of_isRegular
    (M := InfinityMonicModel W) (Polynomial.isRegular_X (R := R))
  have hl : IsLeftRegular (coord W 1 2) := by
    intro a b h
    apply infinityChartToMonic_injective W
    apply hZ
    have he := congrArg (infinityChartToMonic W) h
    have hz : infinityChartToMonic W (coord W 1 2) =
        algebraMap R[X] (InfinityMonicModel W) X := evaluation_coord W 1 _ _ _ 2
    simpa only [map_mul, hz, Algebra.smul_def] using he
  exact ⟨hl, fun a b h => hl (by simpa only [mul_comm] using h)⟩

end FLT.Mazur.WeierstrassIntegralChart
