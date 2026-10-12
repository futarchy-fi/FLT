/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentUnitPointNaturality
public import FLT.Mazur.WeierstrassSplitNodalLaurentCoefficient

/-!
# Actual unit points after changing the coefficient ring

A unit of a coefficient algebra gives the same full Laurent point after
restriction of coefficients. The affine puncture also keeps its coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T B : Type} [CommRing S] [CommRing T] [CommRing B]
  [Algebra S T] [Algebra S B] [Algebra T B] [IsScalarTower S T B] (q : Bˣ)

/-- Restricting coefficients preserves all Laurent functions at the original unit. -/
theorem laurentEvalUnit_coefficient :
    (LaurentUnitPoints.evalUnit (R := T) q).toRingHom.comp
        (nodalLaurentCoefficientMap (algebraMap S T)) =
      (LaurentUnitPoints.evalUnit (R := S) q).toRingHom := by
  have hc (s : S) :
      LaurentUnitPoints.evalUnit (R := T) q
        (nodalLaurentCoefficientMap (algebraMap S T) (LaurentPolynomial.C s)) =
          LaurentUnitPoints.evalUnit (R := S) q (LaurentPolynomial.C s) := by
    rw [show LaurentPolynomial.C s = algebraMap S S[T;T⁻¹] s from rfl,
      nodalLaurentCoefficientMap_scalar, AlgHom.commutes, AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply S T B s).symm
  have hm (s : S) (n : ℤ) :
      LaurentUnitPoints.evalUnit (R := T) q
        (nodalLaurentCoefficientMap (algebraMap S T)
          (LaurentPolynomial.C s * LaurentPolynomial.T n)) =
      LaurentUnitPoints.evalUnit (R := S) q (LaurentPolynomial.C s * LaurentPolynomial.T n) := by
    rw [map_mul, map_mul, map_mul, nodalLaurentCoefficientMap_character, hc]
    rw [LaurentUnitPoints.evalUnit_T, LaurentUnitPoints.evalUnit_T]
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on with
  | h_C s => exact hc s
  | h_add hp hr => simp only [map_add, hp, hr]
  | h_C_mul_T n s _ => exact hm s (n + 1)
  | h_C_mul_T_Z n s _ => exact hm s (-n - 1)

/-- The entire torus point retains its unit when coefficients are restricted. -/
theorem laurentUnitOverPoint_coefficient :
    (laurentUnitOverPoint (R := T) q).left ≫
        Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap (algebraMap S T))) =
      (laurentUnitOverPoint (R := S) q).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (laurentEvalUnit_coefficient (S := S) (T := T) q)

/-- Coefficient change commutes with the inclusion of the entire affine puncture. -/
theorem laurentPolynomialPuncture_coefficient :
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : (Polynomial T) →+* T[T;T⁻¹])) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap S T))) =
      Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap (algebraMap S T))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : (Polynomial S) →+* S[T;T⁻¹])) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro s
    change Polynomial.toLaurent (Polynomial.map (algebraMap S T) (Polynomial.C s)) =
      nodalLaurentCoefficientMap (algebraMap S T) (Polynomial.toLaurent (Polynomial.C s))
    rw [Polynomial.map_C, Polynomial.toLaurent_C, Polynomial.toLaurent_C]
    exact (nodalLaurentCoefficientMap_scalar (algebraMap S T) s).symm
  · change Polynomial.toLaurent (Polynomial.map (algebraMap S T) Polynomial.X) =
      nodalLaurentCoefficientMap (algebraMap S T) (Polynomial.toLaurent Polynomial.X)
    rw [Polynomial.map_X, Polynomial.toLaurent_X, Polynomial.toLaurent_X,
      nodalLaurentCoefficientMap_character]

end FLT.Mazur.WeierstrassIntegralChart
