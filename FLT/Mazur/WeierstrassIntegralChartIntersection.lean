/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Affine intersections in the integral cubic atlas

The gluing universal property identifies each actual chart intersection with
its explicit principal localization. In particular every chart intersection
is compact, and the integral cubic is quasi-separated over any base ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j k : Fin 3)

/-- The specified localization is the actual intersection of two chart inclusions. -/
def integralChartIntersectionIso : overlapScheme W j k ≅
    pullback (integralCurveChart W j) (integralCurveChart W k) :=
  (integralCurveGlueData W).vPullbackConeIsLimit ⟨j⟩ ⟨k⟩ |>.conePointUniqueUpToIso
    (pullback.isLimit _ _)

/-- The intersection comparison preserves the first chart projection. -/
@[reassoc] theorem integralChartIntersectionIso_fst :
    (integralChartIntersectionIso W j k).hom ≫ pullback.fst _ _ =
      overlapInclusion W j k := by
  exact (integralCurveGlueData W).vPullbackConeIsLimit ⟨j⟩ ⟨k⟩ |>.conePointUniqueUpToIso_hom_comp
    (pullback.isLimit _ _) WalkingCospan.left

/-- The intersection comparison preserves the normalized second projection. -/
@[reassoc] theorem integralChartIntersectionIso_snd :
    (integralChartIntersectionIso W j k).hom ≫ pullback.snd _ _ =
      chartTransition W j k ≫ overlapInclusion W k j := by
  exact (integralCurveGlueData W).vPullbackConeIsLimit ⟨j⟩ ⟨k⟩ |>.conePointUniqueUpToIso_hom_comp
    (pullback.isLimit _ _) WalkingCospan.right

/-- Intersections of chart images are exactly images of their principal overlaps. -/
theorem integralChartIntersection_range :
    Set.range (overlapInclusion W j k ≫ integralCurveChart W j) =
      Set.range (integralCurveChart W j) ∩ Set.range (integralCurveChart W k) := by
  rw [← integralChartIntersectionIso_fst_assoc]
  change Set.range ((pullback.fst _ _ ≫ integralCurveChart W j) ∘
    (integralChartIntersectionIso W j k).hom) = _
  rw [Set.range_comp,
    (integralChartIntersectionIso W j k).hom.surjective.range_eq, Set.image_univ]
  exact IsOpenImmersion.range_pullback_to_base_of_left _ _

/-- The compactness needed for quasi-separatedness holds on the concrete atlas. -/
theorem integralChartIntersection_isCompact :
    IsCompact (Set.range (integralCurveChart W j) ∩
      Set.range (integralCurveChart W k)) := by
  rw [← integralChartIntersection_range]
  exact isCompact_range (overlapInclusion W j k ≫ integralCurveChart W j).continuous

/-- The integral cubic is quasi-separated, including over non-noetherian rings. -/
instance integralCurve_quasiSeparatedSpace : QuasiSeparatedSpace (integralCurve W) := by
  apply Scheme.quasiSeparatedSpace_of_isOpenCover
    (fun i => ((integralCurveOpenCover W).f i).opensRange)
    (integralCurveOpenCover W).isOpenCover_opensRange
  · intro i
    exact isAffineOpen_opensRange (integralCurveChart W i.down)
  · intro i l
    exact integralChartIntersection_isCompact W i.down l.down

/-- Combined with local finite presentation and compactness, the model is finitely presented. -/
instance integralCurveStructure_quasiSeparated : QuasiSeparated (integralCurveStructure W) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mpr inferInstance

end FLT.Mazur.WeierstrassIntegralChart
