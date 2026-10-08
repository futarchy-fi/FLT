/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapChartComparison
public import FLT.Mazur.SheafPullbackLocalComparison

/-!
# Actual local module comparisons on the geometric base overlap

Transport the affine effective comparison to the pullbacks of the two fixed
module sheaves on the overlap. The maps are invertible and specialize to the standard affine cover.
Their gluing compatibility will use the independently chosen chart refinements.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CrossRefinement.effectiveComparison
  CrossRefinement.leftChart CrossRefinement.rightChart commonCoverRing commonCoverMap
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p}
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

variable (C C') {A : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C')

/-- The first affine coordinate presents the actual geometric projection. -/
theorem overlapChartLeft_spec :
    f ≫ Limits.pullback.fst C.base C'.base =
      Spec.map (C.overlapChartCrossRefinement C' f).leftBase :=
  (Spec.map_preimage _).symm

/-- The second affine coordinate presents the independent geometric projection. -/
theorem overlapChartRight_spec :
    f ≫ Limits.pullback.snd C.base C'.base =
      Spec.map (C.overlapChartCrossRefinement C' f).rightBase :=
  (Spec.map_preimage _).symm

/-- The effective affine comparison as an actual map between pullbacks on the overlap. -/
def overlapChartLocalComparison :
    (pullback f).obj ((pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D)) ⟶
      (pullback f).obj ((pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D)) :=
  SheafPullbackLocalComparison.transport f (Limits.pullback.fst C.base C'.base)
    (Limits.pullback.snd C.base C'.base)
    (Spec.map (C.overlapChartCrossRefinement C' f).leftBase)
    (Spec.map (C.overlapChartCrossRefinement C' f).rightBase)
    (C.overlapChartLeft_spec C' f) (C.overlapChartRight_spec C' f)
    (C.sheaf D) (C'.sheaf D) ((C.overlapChartCrossRefinement C' f).effectiveComparison D).hom

/-- Local comparisons retain the invertibility of effective affine descent. -/
instance overlapChartLocalComparison_isIso : IsIso (C.overlapChartLocalComparison C' D f) := by
  unfold overlapChartLocalComparison
  infer_instance

/-- The actual local map on each member of the standard base-overlap affine cover. -/
def baseOverlapLocalComparison (i : (C.baseOverlapCover C').I₀) :
    (pullback ((C.baseOverlapCover C').f i)).obj
        ((pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D)) ⟶
      (pullback ((C.baseOverlapCover C').f i)).obj
        ((pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D)) :=
  C.overlapChartLocalComparison C' D ((C.baseOverlapCover C').f i)

/-- Standard overlap-cover maps are isomorphisms before they are glued. -/
instance baseOverlapLocalComparison_isIso (i : (C.baseOverlapCover C').I₀) :
    IsIso (C.baseOverlapLocalComparison C' D i) := by
  unfold baseOverlapLocalComparison
  infer_instance

end FLT.Mazur.SchemeAffineDescent.Chart
