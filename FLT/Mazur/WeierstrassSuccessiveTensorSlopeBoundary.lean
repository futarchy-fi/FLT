/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveTensorSlopeCoordinates
public import FLT.Mazur.PrincipalLocalizationNamedSquare
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Original Laurent boundaries of the constructed tensor polygon branches

Both actual polygon torus opens are exact inverse images of the original
successive tensor boundaries. The comparison keeps every original function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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

local notation "f" => tensorSlopePolygonRetraction W s π b3 b4 b6 S r hr

/-- The entire original left polygon torus maps into its original tensor boundary. -/
def tensorSlopeLeftBoundary : PolygonSmoothing.branchTorus S ⟶
    Spec (.of (Localization.Away (tensorCoord W s π b3 b4 b6 S 0))) :=
  (PolygonSmoothing.leftPunctureIso S (q π)).hom ≫
    PrincipalLocalizationNamedSquare.boundaryMap (f).toRingHom
      (tensorCoord W s π b3 b4 b6 S 0) (PolygonSmoothing.leftCoordinate (q π))
      (tensorSlopePolygonRetraction_left W s π b3 b4 b6 S r hr)

/-- The full left polygon boundary is the exact tensor-boundary inverse image. -/
theorem tensorSlopeLeftBoundary_isPullback :
    IsPullback (tensorSlopeLeftBoundary W s π b3 b4 b6 S r hr)
      (PolygonSmoothing.leftBranchOpen S (q π))
      (PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 0))
      (Spec.map (CommRingCat.ofHom (f).toRingHom)) := by
  have H := PrincipalLocalizationNamedSquare.isPullback (f).toRingHom
    (tensorCoord W s π b3 b4 b6 S 0) (PolygonSmoothing.leftCoordinate (q π))
    (tensorSlopePolygonRetraction_left W s π b3 b4 b6 S r hr)
  exact H.of_iso (PolygonSmoothing.leftPunctureIso S (q π)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [tensorSlopeLeftBoundary])
    (by simp [PolygonSmoothing.leftBranchOpen]; rfl) (by rfl) (by simp)

/-- Restriction along the left boundary keeps the original full tensor comparison. -/
@[reassoc] theorem tensorSlopeLeftBoundary_inclusion :
    tensorSlopeLeftBoundary W s π b3 b4 b6 S r hr ≫
      PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 0) =
        PolygonSmoothing.leftBranchOpen S (q π) ≫
          Spec.map (CommRingCat.ofHom (f).toRingHom) :=
  (tensorSlopeLeftBoundary_isPullback W s π b3 b4 b6 S r hr).w

/-- The entire original right polygon torus maps into its original tensor boundary. -/
def tensorSlopeRightBoundary : PolygonSmoothing.branchTorus S ⟶
    Spec (.of (Localization.Away (tensorCoord W s π b3 b4 b6 S 2))) :=
  (PolygonSmoothing.rightPunctureIso S (q π)).hom ≫
    PrincipalLocalizationNamedSquare.boundaryMap (f).toRingHom
      (tensorCoord W s π b3 b4 b6 S 2) (PolygonSmoothing.rightCoordinate (q π))
      (tensorSlopePolygonRetraction_right W s π b3 b4 b6 S r hr)

/-- The full right polygon boundary is the exact tensor-boundary inverse image. -/
theorem tensorSlopeRightBoundary_isPullback :
    IsPullback (tensorSlopeRightBoundary W s π b3 b4 b6 S r hr)
      (PolygonSmoothing.rightBranchOpen S (q π))
      (PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 2))
      (Spec.map (CommRingCat.ofHom (f).toRingHom)) := by
  have H := PrincipalLocalizationNamedSquare.isPullback (f).toRingHom
    (tensorCoord W s π b3 b4 b6 S 2) (PolygonSmoothing.rightCoordinate (q π))
    (tensorSlopePolygonRetraction_right W s π b3 b4 b6 S r hr)
  exact H.of_iso (PolygonSmoothing.rightPunctureIso S (q π)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [tensorSlopeRightBoundary])
    (by simp [PolygonSmoothing.rightBranchOpen]; rfl) (by rfl) (by simp)

/-- Restriction along the right boundary keeps the original full tensor comparison. -/
@[reassoc] theorem tensorSlopeRightBoundary_inclusion :
    tensorSlopeRightBoundary W s π b3 b4 b6 S r hr ≫
      PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 2) =
        PolygonSmoothing.rightBranchOpen S (q π) ≫
          Spec.map (CommRingCat.ofHom (f).toRingHom) :=
  (tensorSlopeRightBoundary_isPullback W s π b3 b4 b6 S r hr).w

end FLT.Mazur.WeierstrassSuccessiveX
