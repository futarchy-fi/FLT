/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonGeneralizedCurve
public import FLT.Mazur.OneGonSmoothWholeCoefficientAction
public import FLT.Mazur.GeneralizedCurveBaseChangeIso

/-!
# Coefficient comparison of full arithmetic generalized one-gons

The independently constructed arithmetic one-gon over the new coefficient ring
is the categorical pullback as a full generalized elliptic curve. The comparison
retains the original whole cubic, intrinsic group, and action on singular fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (t : R) (ht : IsUnit (1 + 432 * t))

include ht in
/-- The complementary factor stays invertible under arbitrary coefficient extension. -/
theorem coefficientParameter_isUnit : IsUnit (1 + 432 * algebraMap R S t) := by
  simpa only [map_add, map_one, map_mul, map_ofNat] using ht.map (algebraMap R S)

/-- The arithmetic coefficient comparison is an isomorphism of full DR objects. -/
irreducible_def coefficientIso :
    curve (algebraMap R S t) (coefficientParameter_isUnit t ht) ≅
      (curve t ht).baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine isoMk (coefficientCurveOverIso t) (smoothCoefficientGroupOverIso t) ?_ ?_
  · rw [baseChange_inclusion, curve_inclusion]
    exact (coefficientSmoothCurveInclusion t).symm
  · exact coefficientSmoothWholeAction t

/-- The full comparison retains the independently constructed whole-cubic comparison. -/
theorem coefficientIso_curve :
    (coefficientIso (S := S) t ht).hom.curve = (coefficientCurveOverIso t).hom := by
  rw [coefficientIso_def]
  rfl

/-- The full comparison retains the original intrinsic smooth-group comparison. -/
theorem coefficientIso_group :
    (coefficientIso (S := S) t ht).hom.group = (smoothCoefficientGroupOverIso t).hom := by
  rw [coefficientIso_def]
  rfl

/-- Its whole-curve projection is the original coefficient morphism. -/
@[reassoc] theorem coefficientIso_curve_fst :
    (coefficientIso (S := S) t ht).hom.curve.left ≫
      Limits.pullback.fst (family t).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) = coefficientMorphism t := by
  rw [coefficientIso_curve, coefficientCurveOverIso_fst]

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
