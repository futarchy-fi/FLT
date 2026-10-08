/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapLocalComparison
public import FLT.Mazur.SchemeAffineOverlapObjectwiseComparison
public import FLT.Mazur.SheafPullbackNormalizedRefinement

/-!
# Refinement of actual local overlap comparisons

The affine effective comparison square gives refinement of the transported
maps between the restrictions of the two fixed sheaves on the geometric overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open FLT.Mazur.AffineIteratedPullbackSections
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CrossRefinement.effectiveComparison
  CrossRefinement.leftChart CrossRefinement.rightChart commonCoverRing commonCoverMap
  compositeIso
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable {A B : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C')
variable (g : Spec B ⟶ C.baseOverlap C') (α : A ⟶ B) (w : Spec.map α ≫ f = g)

/-- Restriction of the actual local overlap map respects geometric composition. -/
theorem overlapChartLocalComparison_restrict :
    (pullback (Spec.map α)).map (C.overlapChartLocalComparison C' D f) ≫
        (compositeIso (Spec.map α) f g w
          ((pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))).hom =
      (compositeIso (Spec.map α) f g w
          ((pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))).hom ≫
        C.overlapChartLocalComparison C' D g := by
  exact SheafPullbackLocalComparison.transport_refine_objectwise f
    (Limits.pullback.fst C.base C'.base) (Limits.pullback.snd C.base C'.base)
    (Spec.map (C.overlapChartCrossRefinement C' f).leftBase)
    (Spec.map (C.overlapChartCrossRefinement C' f).rightBase)
    (C.overlapChartLeft_spec C' f) (C.overlapChartRight_spec C' f)
    (C.sheaf D) (C'.sheaf D) (Spec.map α) g w
    (Spec.map (C.overlapChartCrossRefinement C' g).leftBase)
    (Spec.map (C.overlapChartCrossRefinement C' g).rightBase)
    ((Spec.map_comp _ α).symm.trans (congrArg Spec.map
      (C.overlapChartCrossRefinement_leftBase C' f g α w)))
    ((Spec.map_comp _ α).symm.trans (congrArg Spec.map
      (C.overlapChartCrossRefinement_rightBase C' f g α w)))
    (C.overlapChartLeft_spec C' g) (C.overlapChartRight_spec C' g)
    _ _ (C.overlapChart_effectiveComparison_objectwise C' D f g α w)

end FLT.Mazur.SchemeAffineDescent.Chart
