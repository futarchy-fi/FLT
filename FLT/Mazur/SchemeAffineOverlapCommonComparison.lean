/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapLocalRefinement
public import FLT.Mazur.SchemeAffineOverlapChartCommonRefinement

/-!
# Actual comparison squares on a common affine cover

Both maps from a constructed common chart refine its local overlap comparison.
These explicit squares supply the two branches of geometric gluing compatibility.
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
variable {A B : CommRingCat.{u}}
variable (f : Spec A ⟶ C.baseOverlap C') (g : Spec B ⟶ C.baseOverlap C')
variable (i : (C.overlapChartCommonCover C' f g).I₀)

/-- The left branch gives the actual comparison on the constructed common chart. -/
theorem overlapChartLocalComparison_common_left :
    (pullback (Spec.map (C.overlapChartCommonLeft C' f g i))).map
        (C.overlapChartLocalComparison C' D f) ≫
        (compositeIso (Spec.map (C.overlapChartCommonLeft C' f g i)) f
          (C.overlapChartCommonMap C' f g i) (C.overlapChartCommonLeft_over C' f g i)
          ((pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))).hom =
      (compositeIso (Spec.map (C.overlapChartCommonLeft C' f g i)) f
          (C.overlapChartCommonMap C' f g i) (C.overlapChartCommonLeft_over C' f g i)
          ((pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))).hom ≫
        C.overlapChartLocalComparison C' D (C.overlapChartCommonMap C' f g i) :=
  C.overlapChartLocalComparison_restrict C' D f (C.overlapChartCommonMap C' f g i)
    (C.overlapChartCommonLeft C' f g i) (C.overlapChartCommonLeft_over C' f g i)

/-- The right branch gives the actual comparison on the constructed common chart. -/
theorem overlapChartLocalComparison_common_right :
    (pullback (Spec.map (C.overlapChartCommonRight C' f g i))).map
        (C.overlapChartLocalComparison C' D g) ≫
        (compositeIso (Spec.map (C.overlapChartCommonRight C' f g i)) g
          (C.overlapChartCommonMap C' f g i) (C.overlapChartCommonRight_over C' f g i)
          ((pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))).hom =
      (compositeIso (Spec.map (C.overlapChartCommonRight C' f g i)) g
          (C.overlapChartCommonMap C' f g i) (C.overlapChartCommonRight_over C' f g i)
          ((pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))).hom ≫
        C.overlapChartLocalComparison C' D (C.overlapChartCommonMap C' f g i) :=
  C.overlapChartLocalComparison_restrict C' D g (C.overlapChartCommonMap C' f g i)
    (C.overlapChartCommonRight C' f g i) (C.overlapChartCommonRight_over C' f g i)

end FLT.Mazur.SchemeAffineDescent.Chart
