/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The actual affine chart and the monic Weierstrass coordinate ring

Compare the existing three-coordinate quotient with mathlib's monic quadratic
in Y over R[X]. Both maps are explicit and preserve the normalized coordinates.
-/

@[expose] public noncomputable section

open Polynomial WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluation of the affine monic polynomial in an arbitrary coefficient algebra. -/
theorem affineMonicPolynomial_eval {S : Type*} [CommRing S]
    (f : R[X] →+* S) (y : S) :
    W.toAffine.polynomial.eval₂ f y =
      y ^ 2 + (f (C W.a₁) * f X + f (C W.a₃)) * y -
        (f X ^ 3 + f (C W.a₂) * f X ^ 2 + f (C W.a₄) * f X + f (C W.a₆)) := by
  simp only [Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, map_add, map_mul, map_pow]

/-- The monic coordinate ring carries the original normalized projective point. -/
theorem affineMonicModel_equation :
    (W.map (algebraMap R W.toAffine.CoordinateRing)).toProjective.Equation
      ![algebraMap R[X] W.toAffine.CoordinateRing X,
        AdjoinRoot.root W.toAffine.polynomial, 1] := by
  have h := AdjoinRoot.eval₂_root W.toAffine.polynomial
  change W.toAffine.polynomial.eval₂ (algebraMap R[X] W.toAffine.CoordinateRing)
    (AdjoinRoot.root W.toAffine.polynomial) = 0 at h
  rw [affineMonicPolynomial_eval] at h
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  have hc (a : R) : algebraMap R[X] W.toAffine.CoordinateRing (C a) =
      algebraMap R W.toAffine.CoordinateRing a :=
    (IsScalarTower.algebraMap_apply R R[X] W.toAffine.CoordinateRing a).symm
  simp only [hc] at h
  linear_combination h

/-- Send the original affine chart to the existing monic model. -/
def affineChartToMonic : Coordinate W 2 →ₐ[R] W.toAffine.CoordinateRing :=
  evaluation W 2 ![algebraMap R[X] W.toAffine.CoordinateRing X,
    AdjoinRoot.root W.toAffine.polynomial, 1] (affineMonicModel_equation W) rfl

/-- The original affine coordinates satisfy the monic quadratic. -/
theorem affineMonicPolynomial_chart_root :
    W.toAffine.polynomial.eval₂ (aeval (coord W 2 0)).toRingHom (coord W 2 1) = 0 := by
  rw [affineMonicPolynomial_eval]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, aeval_X]
  have h := coord_equation W 2
  rw [Projective.equation_iff] at h
  simp only [coord_self, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  linear_combination h

/-- Evaluate the monic model back in the actual affine chart. -/
def affineMonicToChart : W.toAffine.CoordinateRing →ₐ[R] Coordinate W 2 :=
  AdjoinRoot.liftAlgHom W.toAffine.polynomial (aeval (coord W 2 0))
    (coord W 2 1) (affineMonicPolynomial_chart_root W)

/-- The monic comparison is a retraction on the original quotient. -/
theorem affineMonicToChart_comp :
    (affineMonicToChart W).comp (affineChartToMonic W) = AlgHom.id R (Coordinate W 2) := by
  apply hom_ext
  intro i
  fin_cases i <;>
    simp [affineChartToMonic, affineMonicToChart, AdjoinRoot.algebraMap_eq, coord_self,
      AdjoinRoot.liftAlgHom_root, AdjoinRoot.liftAlgHom_of]

/-- The monic comparison also fixes the two generators on the other side. -/
theorem affineChartToMonic_comp :
    (affineChartToMonic W).comp (affineMonicToChart W) =
      AlgHom.id R W.toAffine.CoordinateRing := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change affineChartToMonic W
      (affineMonicToChart W (AdjoinRoot.of W.toAffine.polynomial X)) =
        AdjoinRoot.of W.toAffine.polynomial X
    rw [affineMonicToChart, AdjoinRoot.liftAlgHom_of, aeval_X]
    exact evaluation_coord W 2 _ _ _ 0
  · change affineChartToMonic W
      (affineMonicToChart W (AdjoinRoot.root W.toAffine.polynomial)) =
        AdjoinRoot.root W.toAffine.polynomial
    rw [affineMonicToChart, AdjoinRoot.liftAlgHom_root]
    exact evaluation_coord W 2 _ _ _ 1

/-- The actual affine chart is explicitly equivalent to mathlib's monic coordinate ring. -/
def affineChartMonicEquiv : Coordinate W 2 ≃ₐ[R] W.toAffine.CoordinateRing :=
  AlgEquiv.ofAlgHom (affineChartToMonic W) (affineMonicToChart W)
    (affineChartToMonic_comp W) (affineMonicToChart_comp W)

end FLT.Mazur.WeierstrassIntegralChart
