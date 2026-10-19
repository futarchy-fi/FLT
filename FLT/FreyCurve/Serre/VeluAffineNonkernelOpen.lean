/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineRationalRepresentative
public import FLT.FreyCurve.Serre.VeluEvaluation

/-!
# The explicit Vélu open contains every original affine nonkernel point

Nonvanishing of the actual reduced denominators factors the original point
through the principal localization, hence through the rational map's domain.
-/

@[expose] public noncomputable section

open scoped Polynomial
open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  {x y : K} (hP : E.toAffine.Nonsingular x y)

/-- The original affine point evaluated on the actual source chart. -/
def veluSourcePointChart : Coordinate E 2 →ₐ[K] K :=
  evaluation E 2 ![x, y, 1]
    ((Projective.equation_some _ _).mpr (by simpa using hP.left)) rfl

omit [DecidableEq K] in
/-- Polynomial functions of the original x-coordinate evaluate at the same x. -/
theorem veluSourcePointChart_polynomial (p : K[X]) :
    veluSourcePointChart E hP (Polynomial.aeval (coord E 2 0) p) = p.eval x := by
  rw [← Polynomial.aeval_algHom_apply, veluSourcePointChart, evaluation_coord]
  rfl

/-- The actual common denominator does not vanish away from the original kernel. -/
theorem veluSourcePointChart_denominator (hPG : Affine.Point.some x y hP ∉ G) :
    veluSourcePointChart E hP (veluAffineDenominator E G) ≠ 0 := by
  rw [veluAffineDenominator, veluSourcePointChart_polynomial, Polynomial.eval_mul]
  have hx := x_not_mem_kernelAbscissae E G hP hPG
  exact mul_ne_zero (regular_eval_xFunction E G x hx).1
    (regular_eval_slopeFunction E G x hx).1

/-- The original nonkernel point evaluates the explicit principal localization. -/
def veluAffinePointLift (hPG : Affine.Point.some x y hP ∉ G) :
    VeluAffineLocalization E G →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (veluAffineDenominator E G)
    (isUnit_iff_ne_zero.mpr (veluSourcePointChart_denominator E G hP hPG))

/-- Evaluation on the localization retains all original source affine functions. -/
@[simp] theorem veluAffinePointLift_algebraMap (hPG : Affine.Point.some x y hP ∉ G)
    (a : Coordinate E 2) :
    veluAffinePointLift E G hP hPG (algebraMap _ (VeluAffineLocalization E G) a) =
      veluSourcePointChart E hP a :=
  IsLocalization.Away.lift_eq _
    (isUnit_iff_ne_zero.mpr (veluSourcePointChart_denominator E G hP hPG)) a

/-- The original point as a scheme morphism factors through the denominator open. -/
@[reassoc] theorem veluAffinePointLift_source (hPG : Affine.Point.some x y hP ∉ G) :
    Spec.map (CommRingCat.ofHom (veluAffinePointLift E G hP hPG).toRingHom) ≫
        veluAffineOpenImmersion E G =
      Spec.map (CommRingCat.ofHom (veluSourcePointChart E hP).toRingHom) ≫
        integralCurveChart E 2 := by
  rw [veluAffineOpenImmersion, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact veluAffinePointLift_algebraMap E G hP hPG a

/-- Every original affine nonkernel point belongs to the explicit regular open. -/
theorem veluAffineNonkernel_mem_open (hPG : Affine.Point.some x y hP ∉ G)
    (z : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom (veluSourcePointChart E hP).toRingHom) ≫
      integralCurveChart E 2) z ∈ (veluAffineOpenImmersion E G).opensRange := by
  rw [← veluAffinePointLift_source E G hP hPG]
  exact ⟨_, rfl⟩

variable [CharZero K]

/-- The original Vélu rational map is defined at every original affine nonkernel point. -/
theorem veluAffineNonkernel_mem_rationalDomain (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (hPG : Affine.Point.some x y hP ∉ G) (z : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom (veluSourcePointChart E hP).toRingHom) ≫
      integralCurveChart E 2) z ∈ (veluSchemeRationalMap E G hodd).domain :=
  veluAffineOpen_le_rationalDomain E G hodd (veluAffineNonkernel_mem_open E G hP hPG z)

end WeierstrassCurve.Velu
