/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineImmersionSectionCoordinates
public import FLT.Mazur.WeierstrassOriginDivisorCoordinates
public import FLT.Mazur.WeierstrassOriginPunctureIntersection

/-!
# The original origin charts as actual affine opens

The parameter neighborhood, affine chart, and puncture give actual affine
opens on the cubic. Their section coordinates retain the original ring maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.AffineImmersionSectionCoordinates

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original parameter neighborhood viewed as an affine open of the cubic. -/
abbrev originImageOpen : (integralCurve W).affineOpens :=
  imageAffine (originNeighborhoodInclusion W)

/-- The original affine chart viewed as an affine open of the cubic. -/
abbrev originAffineOpen : (integralCurve W).affineOpens :=
  imageAffine (integralCurveChart W 2)

/-- The original puncture inclusion into the cubic. -/
def originPunctureToCurve : Spec (.of (OriginPuncture W)) ⟶ integralCurve W :=
  PrincipalAffineRefinement.inclusion (originCoordinate W 0) ≫ originNeighborhoodInclusion W

instance originPunctureToCurve_isOpenImmersion : IsOpenImmersion (originPunctureToCurve W) :=
  inferInstanceAs (IsOpenImmersion
    (PrincipalAffineRefinement.inclusion (originCoordinate W 0) ≫ originNeighborhoodInclusion W))

/-- The actual overlap as an affine open in the original cubic. -/
abbrev originOverlapOpen : (integralCurve W).affineOpens :=
  imageAffine (originPunctureToCurve W)

/-- The puncture image is the full intersection of the two original affine image opens. -/
theorem originOverlapOpen_eq :
    (originOverlapOpen W).1 = (originImageOpen W).1 ⊓ (originAffineOpen W).1 := by
  change (PrincipalAffineRefinement.inclusion (originCoordinate W 0) ≫
    originNeighborhoodInclusion W) ''ᵁ ⊤ =
    originNeighborhoodInclusion W ''ᵁ ⊤ ⊓ integralCurveChart W 2 ''ᵁ ⊤
  simp only [Scheme.Hom.image_top_eq_opensRange]
  rw [Scheme.Hom.opensRange_comp, ← originNeighborhood_affine_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

/-- The original two image opens cover the entire cubic. -/
theorem originImageOpen_sup_affine :
    (originImageOpen W).1 ⊔ (originAffineOpen W).1 = ⊤ := by
  apply top_le_iff.mp
  intro x _
  change x ∈ (originNeighborhoodInclusion W ''ᵁ ⊤) ⊔ (integralCurveChart W 2 ''ᵁ ⊤)
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  change x ∈ Set.range (originNeighborhoodInclusion W) ∨
    x ∈ Set.range (integralCurveChart W 2)
  exact originNeighborhood_affine_cover W x

/-- Inclusion of the actual intersection in the parameter neighborhood. -/
theorem originOverlapOpen_le_image : (originOverlapOpen W).1 ≤ (originImageOpen W).1 := by
  rw [originOverlapOpen_eq]
  exact inf_le_left

/-- Inclusion of the actual intersection in the original affine chart. -/
theorem originOverlapOpen_le_affine : (originOverlapOpen W).1 ≤ (originAffineOpen W).1 := by
  rw [originOverlapOpen_eq]
  exact inf_le_right

/-- Restriction from the parameter image open is the original localization homomorphism. -/
theorem originImageCoordinates_restrict (s : Γ(integralCurve W, (originImageOpen W).1)) :
    coordinates (originPunctureToCurve W)
      ((integralCurve W).presheaf.map (homOfLE (originOverlapOpen_le_image W)).op s) =
      algebraMap (OriginNeighborhood W) (OriginPuncture W)
        (coordinates (originNeighborhoodInclusion W) s) :=
  coordinates_restrict _ _ _ rfl s

/-- Restriction from the affine image open is the original map used in the pole bound. -/
theorem originAffineCoordinates_restrict (s : Γ(integralCurve W, (originAffineOpen W).1)) :
    coordinates (originPunctureToCurve W)
      ((integralCurve W).presheaf.map (homOfLE (originOverlapOpen_le_affine W)).op s) =
      originPunctureAffine W (coordinates (integralCurveChart W 2) s) :=
  coordinates_restrict _ _ _ (originPuncture_inclusion W).symm s

end FLT.Mazur.WeierstrassIntegralChart
