/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXIncidenceNodeMap
public import FLT.Mazur.WeierstrassModificationXLaurentEvaluation
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# The exact original Laurent boundary of the incidence morphism

Every original Laurent slope gives t = T⁻¹ and x = sT. The complete boundary
therefore commutes with edge inversion, without dropping nilpotent terms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[T;T⁻¹]) (hr : r ^ 2 + laurentSlopeLinear W b3 * r =
    laurentSlopeConstant W s b4 b6)
local notation "E" => laurentSlopeEvaluation W s b3 b4 b6 r hr

/-- The original horizontal coordinate is exactly s times the Laurent edge coordinate. -/
@[simp] theorem laurentSlopeEvaluation_x :
    E (x W s b3 b4 b6) = LaurentPolynomial.C s * LaurentPolynomial.T 1 := by
  have h := congrArg E (incidence W s b3 b4 b6)
  rw [map_mul, laurentSlopeEvaluation_t, AlgHom.commutes] at h
  apply (LaurentPolynomial.isUnit_T (-1)).mul_left_cancel
  rw [h, mul_left_comm, ← LaurentPolynomial.T_add]
  simp only [Int.reduceNeg, Int.reduceAdd, LaurentPolynomial.T_zero, mul_one]
  exact (LaurentPolynomial.C_eq_algebraMap s).symm

/-- All original functions agree with the inverse parameter on the standard polygon puncture. -/
theorem incidencePolygonMap_laurent :
    (E).comp (incidencePolygonMap W s b3 b4 b6) =
      LaurentPolynomial.invert.toAlgHom.comp (PolygonSmoothing.leftLaurentMap s) := by
  apply PolygonSmoothing.chartRing_hom_ext s
  · simp only [AlgHom.comp_apply, incidencePolygonMap_left, laurentSlopeEvaluation_t,
      PolygonSmoothing.leftLaurentMap_left]
    simp
  · simp only [AlgHom.comp_apply, incidencePolygonMap_right, laurentSlopeEvaluation_x,
      PolygonSmoothing.leftLaurentMap_right]
    simp

/-- The full original Laurent morphism has the required inverse edge parameter. -/
@[reassoc] theorem incidencePolygonMorphism_laurent :
    Spec.map (CommRingCat.ofHom (E).toRingHom) ≫
      incidencePolygonMorphism W s b3 b4 b6 =
        (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.leftBranchOpen R s := by
  rw [incidencePolygonMorphism, PolygonSmoothing.leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g.toRingHom))
    (incidencePolygonMap_laurent W s b3 b4 b6 r hr)

end FLT.Mazur.WeierstrassModificationX
