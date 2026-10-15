/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveTensorSlopeBoundary
public import FLT.Mazur.PolygonSmoothingNilpotentBranches

/-!
# Laurent evaluation on the full original tensor boundaries

These algebra maps are the original tensor branch maps on spectra. The
older left evaluation includes exactly the polygon atlas edge inversion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S π) (algebraMap R S b4) (algebraMap R S b6))
local notation "q" => algebraMap R S
local notation "ev" => tensorSlopePolygonRetraction W s π b3 b4 b6 S r hr

/-- The full old tensor localization evaluates in the inverse Laurent coordinate. -/
def tensorInverseLeftSlopeLaurent :
    Localization.Away (tensorCoord W s π b3 b4 b6 S 0) →ₐ[S] S[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (tensorCoord W s π b3 b4 b6 S 0)
    (f := LaurentPolynomial.invert.toAlgHom.comp ((PolygonSmoothing.leftLaurentMap (q π)).comp ev))
    (by
      simp only [AlgHom.comp_apply, tensorSlopePolygonRetraction_left,
        PolygonSmoothing.leftLaurentMap_left, AlgEquiv.coe_toAlgHom,
        LaurentPolynomial.invert_T, Int.reduceNeg]
      exact LaurentPolynomial.isUnit_T (-1))

/-- The full next tensor localization evaluates in its original right coordinate. -/
def tensorRightSlopeLaurent :
    Localization.Away (tensorCoord W s π b3 b4 b6 S 2) →ₐ[S] S[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (tensorCoord W s π b3 b4 b6 S 2)
    (f := ((PolygonSmoothing.leftLaurentMap (q π)).comp
      (PolygonSmoothing.branchSwapMap (q π))).comp ev) (by
        simp only [AlgHom.comp_apply, tensorSlopePolygonRetraction_right,
          PolygonSmoothing.branchSwapMap_right, PolygonSmoothing.leftLaurentMap_left]
        exact LaurentPolynomial.isUnit_T 1)

/-- The inverse-left evaluation keeps all original tensor functions. -/
theorem tensorInverseLeftSlopeLaurent_base (z : ScalarExtension W s π b3 b4 b6 S) :
    tensorInverseLeftSlopeLaurent W s π b3 b4 b6 S r hr (algebraMap _ _ z) =
      LaurentPolynomial.invert (PolygonSmoothing.leftLaurentMap (q π) (ev z)) := by
  rw [tensorInverseLeftSlopeLaurent, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The right evaluation keeps all original tensor functions. -/
theorem tensorRightSlopeLaurent_base (z : ScalarExtension W s π b3 b4 b6 S) :
    tensorRightSlopeLaurent W s π b3 b4 b6 S r hr (algebraMap _ _ z) =
      PolygonSmoothing.leftLaurentMap (q π) (PolygonSmoothing.branchSwapMap (q π) (ev z)) := by
  rw [tensorRightSlopeLaurent, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- On spectra the inverse-left evaluation is exactly the original inverted tensor boundary. -/
theorem tensorInverseLeftSlopeLaurent_spec :
    Spec.map (CommRingCat.ofHom
      (tensorInverseLeftSlopeLaurent W s π b3 b4 b6 S r hr).toRingHom) =
    (PolygonSmoothing.edgeInversion S).hom ≫ tensorSlopeLeftBoundary W s π b3 b4 b6 S r hr := by
  apply (cancel_mono (PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 0))).mp
  rw [Category.assoc, tensorSlopeLeftBoundary_inclusion]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change ScalarExtension W s π b3 b4 b6 S at z
  change tensorInverseLeftSlopeLaurent W s π b3 b4 b6 S r hr (algebraMap _ _ z) =
    LaurentPolynomial.invert (PolygonSmoothing.leftPunctureToLaurent (q π)
      (algebraMap _ _ (ev z)))
  rw [tensorInverseLeftSlopeLaurent_base, PolygonSmoothing.leftPunctureToLaurent_map]

/-- On spectra the right evaluation is exactly the original full tensor boundary. -/
theorem tensorRightSlopeLaurent_spec :
    Spec.map (CommRingCat.ofHom (tensorRightSlopeLaurent W s π b3 b4 b6 S r hr).toRingHom) =
      tensorSlopeRightBoundary W s π b3 b4 b6 S r hr := by
  apply (cancel_mono (PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 2))).mp
  rw [tensorSlopeRightBoundary_inclusion]
  change Spec.map _ ≫ Spec.map _ = (Spec.map _ ≫ Spec.map _) ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change ScalarExtension W s π b3 b4 b6 S at z
  change tensorRightSlopeLaurent W s π b3 b4 b6 S r hr (algebraMap _ _ z) =
    PolygonSmoothing.rightPunctureEquiv (q π) (algebraMap _ _ (ev z))
  rw [tensorRightSlopeLaurent_base]
  change _ = PolygonSmoothing.leftPunctureToLaurent (q π)
    (PolygonSmoothing.rightToLeftPuncture (q π) (algebraMap _ _ _))
  rw [PolygonSmoothing.rightToLeftPuncture_map, PolygonSmoothing.leftPunctureToLaurent_map]

end FLT.Mazur.WeierstrassSuccessiveX
