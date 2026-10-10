/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginNeighborhoodCover
public import FLT.Mazur.WeierstrassOriginPoleBounds

/-!
# The pole calculations use the original scheme overlap

The punctured parameter neighborhood maps to both original charts. Their
maps to the original cubic are equal, and the puncture inclusion into the
parameter neighborhood retains that same morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The pole-coordinate algebra map is exactly the original change of scheme charts. -/
theorem originPunctureAffine_scheme :
    Spec.map (CommRingCat.ofHom (originPunctureAffine W).toRingHom) ≫ integralCurveChart W 2 =
      Spec.map (CommRingCat.ofHom (originPunctureChart W).toRingHom) ≫ integralCurveChart W 1 := by
  change Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom ≫
    CommRingCat.ofHom (originPunctureOverlap W).toRingHom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, integralCurve_output_transition, ← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (originPunctureOverlap W).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (overlapRestriction W 1 2).toRingHom)) ≫ _ = _
  rw [← Spec.map_comp]
  have he := overlapLift_restriction W 1 2 (originPunctureChart W) (originPuncture_z_isUnit W)
  change Spec.map (CommRingCat.ofHom
    ((originPunctureOverlap W).comp (overlapRestriction W 1 2)).toRingHom) ≫ _ = _
  rw [show (originPunctureOverlap W).comp (overlapRestriction W 1 2) =
    originPunctureChart W from he]

/-- The original parameter puncture inclusion agrees with its affine-chart morphism. -/
theorem originPuncture_inclusion :
    PrincipalAffineRefinement.inclusion (originCoordinate W 0) ≫
        originNeighborhoodInclusion W =
      Spec.map (CommRingCat.ofHom (originPunctureAffine W).toRingHom) ≫
        integralCurveChart W 2 := by
  rw [originPunctureAffine_scheme]
  unfold originNeighborhoodInclusion PrincipalAffineRefinement.chart
    PrincipalAffineRefinement.inclusion
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2

end FLT.Mazur.WeierstrassIntegralChart
