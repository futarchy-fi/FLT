/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentScaledCoordinateIsomorphisms
public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Scaling the original cyclic Laurent coordinates

An arithmetic reciprocal coordinate becomes inverse scaling when expressed
in the cyclic normalization's already inverted parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonScaledReciprocal
set_option backward.isDefEq.respectTransparency false
universe u
variable {F : Type u} [Field F]

/-- Reciprocal substitution followed by inversion has the inverse coefficient scale. -/
theorem reciprocal_comp_invert (a : Fˣ) :
    (reciprocal a).comp LaurentPolynomial.invert.toAlgHom = scaling a⁻¹ := by
  apply AlgHom.coe_ringHom_injective
  apply PolygonScalingNaturality.ringHom_ext
  · intro c
    change reciprocal a (LaurentPolynomial.invert (LaurentPolynomial.C c)) =
      scaling a⁻¹ (LaurentPolynomial.C c)
    rw [LaurentPolynomial.invert_C, reciprocal_C]
    exact ((scaling a⁻¹).commutes c).symm
  · change reciprocal a (LaurentPolynomial.invert (LaurentPolynomial.T 1)) = _
    rw [LaurentPolynomial.invert_T, reciprocal_T_inv]
    exact (PolygonChartScaling.laurent_T_one a⁻¹).symm
  · change reciprocal a (LaurentPolynomial.invert (LaurentPolynomial.T (-1))) = _
    rw [LaurentPolynomial.invert_T]
    change reciprocal a (LaurentPolynomial.T 1) = _
    rw [reciprocal_T]
    change LaurentPolynomial.C (a : F) * LaurentPolynomial.T (-1) =
      PolygonChartScaling.laurent a⁻¹ (LaurentPolynomial.T (-1))
    simpa only [inv_inv] using (PolygonChartScaling.laurent_T_neg_one a⁻¹).symm

/-- The arithmetic reciprocal followed by cyclic inversion is a simple scaling. -/
@[reassoc] theorem reciprocal_spec_inversion (a : Fˣ) :
    Spec.map (CommRingCat.ofHom (reciprocal a).toRingHom) ≫
        (ProjectiveLine.inversion F).hom =
      Spec.map (CommRingCat.ofHom (scaling a⁻¹).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact congrArg (fun f : F[T;T⁻¹] →ₐ[F] F[T;T⁻¹] => CommRingCat.ofHom f.toRingHom)
    (reciprocal_comp_invert a)

/-- Inverse scaling before the original cyclic inversion gives the arithmetic reciprocal. -/
@[reassoc] theorem inverse_scaling_spec_inversion (a : Fˣ) :
    Spec.map (CommRingCat.ofHom (scaling a⁻¹).toRingHom) ≫
        (ProjectiveLine.inversion F).hom =
      Spec.map (CommRingCat.ofHom (reciprocal a).toRingHom) := by
  rw [← reciprocal_spec_inversion, Category.assoc]
  change _ ≫ (ProjectiveLine.inversion F).hom ≫ (ProjectiveLine.inversion F).inv = _
  rw [Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.PolygonScaledReciprocal
