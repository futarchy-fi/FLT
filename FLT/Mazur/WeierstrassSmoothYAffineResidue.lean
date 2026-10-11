/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothYAffineSource
public import FLT.Mazur.WeierstrassInfinityResidueTensor

/-!
# The named smooth Laurent parameter on the integral affine/Y source

The residue map is constructed from the original infinity tensor equivalence.
The derivative becomes the Laurent unit; only the actual Z coordinate is
then inverted to give the affine part of this named smooth parameter.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "a" => WeierstrassDilatation.residueTangentUnit D

/-- The original Y chart evaluated on its actual named smooth residue parameter. -/
def smoothYParameterResidue : Coordinate W 1 →ₐ[R] K[T;T⁻¹] :=
  ((infinityResidueEquiv D hdepth).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The original projective coordinates retain their named Laurent values. -/
theorem smoothYParameterResidue_coord (i : Fin 3) :
    smoothYParameterResidue D hdepth (coord W 1 i) =
      ![splitNodalLaurentX a, 1, splitNodalLaurentZ a] i :=
  infinityResidueEquiv_coord D hdepth i

/-- The free derivative is precisely the invertible named Laurent parameter. -/
theorem smoothYParameterResidue_partial :
    smoothYParameterResidue D hdepth (chartPartial W 1 2) = LaurentPolynomial.T 1 := by
  rw [chartPartial_map]
  have he : W.map (algebraMap R K[T;T⁻¹]) =
      (splitNodalEquation a).map (algebraMap K K[T;T⁻¹]) := by
    rw [← splitDepth_residue_equation D hdepth, WeierstrassCurve.map_map,
      ← IsScalarTower.algebraMap_eq]
  rw [he]
  change MvPolynomial.eval _
    ((splitNodalEquation a).map (algebraMap K K[T;T⁻¹])).toProjective.polynomialZ = _
  rw [WeierstrassCurve.Projective.eval_polynomialZ]
  simp only [Function.comp_apply, smoothYParameterResidue_coord,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    splitNodalEquation, WeierstrassCurve.map, WeierstrassCurve.toProjective,
    map_zero, one_pow, mul_one, mul_zero, zero_mul, add_zero, sub_zero]
  exact splitNodalLaurent_tangent a

/-- The actual affine part of the named smooth parameter. -/
abbrev SmoothYParameterRing := Localization.Away (splitNodalLaurentZ a)

/-- The named parameter lifts through the actual derivative localization. -/
def smoothYDerivativeResidue : SmoothYDerivativeRing W →ₐ[R] K[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (f := smoothYParameterResidue D hdepth)
    (chartPartial W 1 2) (by
      rw [smoothYParameterResidue_partial]
      exact LaurentPolynomial.isUnit_T 1)

/-- The derivative lift retains every original Y-chart function. -/
theorem smoothYDerivativeResidue_base (q : Coordinate W 1) :
    smoothYDerivativeResidue D hdepth
      (algebraMap (Coordinate W 1) (SmoothYDerivativeRing W) q) =
        smoothYParameterResidue D hdepth q :=
  IsLocalization.Away.lift_eq _ (by
    change IsUnit (smoothYParameterResidue D hdepth (chartPartial W 1 2))
    rw [smoothYParameterResidue_partial]
    exact LaurentPolynomial.isUnit_T 1) q

/-- The residue map from the constructed integral common smooth source. -/
def smoothYAffineResidue : SmoothYAffineRing W →ₐ[R] SmoothYParameterRing D :=
  IsLocalization.Away.liftAlgHom
    (f := (IsScalarTower.toAlgHom R K[T;T⁻¹] (SmoothYParameterRing D)).comp
      (smoothYDerivativeResidue D hdepth))
    (algebraMap (Coordinate W 1) (SmoothYDerivativeRing W) (coord W 1 2)) (by
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', smoothYDerivativeResidue_base,
        smoothYParameterResidue_coord, Matrix.cons_val_two]
      change IsUnit (algebraMap K[T;T⁻¹] (SmoothYParameterRing D) (splitNodalLaurentZ a))
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- The affine residue lift preserves every original normalized Y function. -/
theorem smoothYAffineResidue_base (q : Coordinate W 1) :
    smoothYAffineResidue D hdepth (smoothYAffineY W q) =
      algebraMap K[T;T⁻¹] (SmoothYParameterRing D) (smoothYParameterResidue D hdepth q) := by
  change smoothYAffineResidue D hdepth
    (algebraMap (SmoothYDerivativeRing W) (SmoothYAffineRing W)
      (algebraMap (Coordinate W 1) (SmoothYDerivativeRing W) q)) = _
  unfold smoothYAffineResidue
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  change algebraMap K[T;T⁻¹] (SmoothYParameterRing D)
    (smoothYDerivativeResidue D hdepth
      (algebraMap (Coordinate W 1) (SmoothYDerivativeRing W) q)) = _
  rw [smoothYDerivativeResidue_base]

end FLT.Mazur.WeierstrassIntegralChart
