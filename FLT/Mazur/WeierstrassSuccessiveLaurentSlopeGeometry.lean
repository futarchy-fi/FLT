/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveAdjacentSlopeOverlap
public import FLT.Mazur.WeierstrassSuccessiveXHorizontalScheme
public import FLT.Mazur.PolygonSmoothingNilpotentBranches

/-!
# The localized slope evaluations are the original polygon boundary morphisms

Taking spectra retains the actual Laurent opens and the atlas edge inversion.
The equalities hold as scheme morphisms, on every original function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (r : SuccessiveIncidence.Coordinate π)
  (hr : r ^ 2 + nodeSlopeLinear W π b3 * r = nodeSlopeConstant W s π b4 b6)

/-- The entire localized inverse-left comparison is the original inverted polygon boundary. -/
@[reassoc] theorem inverseLeftSlopeLaurent_spec_inclusion :
    Spec.map (CommRingCat.ofHom (inverseLeftSlopeLaurent W s π b3 b4 b6 r hr).toRingHom) ≫
      xOpenInclusion W s π b3 b4 b6 =
    (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.leftBranchOpen R π ≫
      simpleSlopePolygonChart W s π b3 b4 b6 r hr := by
  change Spec.map _ ≫ Spec.map _ =
    Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) ≫ (Spec.map _ ≫ Spec.map _)
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change inverseLeftSlopeLaurent W s π b3 b4 b6 r hr (algebraMap _ _ z) =
    LaurentPolynomial.invert (PolygonSmoothing.leftPunctureToLaurent π
      (algebraMap _ _ (SuccessiveIncidence.toPolygon π
        (simpleSlopeRetraction W s π b3 b4 b6 r hr z))))
  rw [inverseLeftSlopeLaurent_base, PolygonSmoothing.leftPunctureToLaurent_map]
  rfl

/-- The entire localized right comparison is the original right polygon boundary. -/
@[reassoc] theorem rightSlopeLaurent_spec_inclusion :
    Spec.map (CommRingCat.ofHom (rightSlopeLaurent W s π b3 b4 b6 r hr).toRingHom) ≫
      horizontalOpenInclusion W s π b3 b4 b6 =
    PolygonSmoothing.rightBranchOpen R π ≫ simpleSlopePolygonChart W s π b3 b4 b6 r hr := by
  change Spec.map _ ≫ Spec.map _ =
    (Spec.map _ ≫ Spec.map _) ≫ (Spec.map _ ≫ Spec.map _)
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change rightSlopeLaurent W s π b3 b4 b6 r hr (algebraMap _ _ z) =
    PolygonSmoothing.rightPunctureEquiv π (algebraMap _ _
      (SuccessiveIncidence.toPolygon π (simpleSlopeRetraction W s π b3 b4 b6 r hr z)))
  rw [rightSlopeLaurent_base]
  change _ = PolygonSmoothing.leftPunctureToLaurent π
    (PolygonSmoothing.rightToLeftPuncture π (algebraMap _ _ _))
  rw [PolygonSmoothing.rightToLeftPuncture_map, PolygonSmoothing.leftPunctureToLaurent_map]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
