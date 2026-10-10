/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenCoverGluingIso
public import FLT.Mazur.SchemeAffineOverlapLocalRefinement

/-!
# Gluing effective affine comparisons on the geometric overlap

Constructed common affine charts cover each intersection of standard overlap
charts. Refinement of the actual local maps supplies compatibility, so the
invertible effective comparisons glue to an isomorphism on the entire overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CrossRefinement.effectiveComparison sheaf
  overlapChartLocalComparison
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- The standard overlap-chart maps are compatible on their entire open intersections. -/
theorem baseOverlapLocalComparison_compatible :
    ModuleSheafOpenImmersionGluing.Compatible
      (M := (pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))
      (N := (pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))
      (fun i ↦ Spec ((C.baseOverlapCover C').X i)) (C.baseOverlapCover C').f
      (fun i ↦ C.overlapChartLocalComparison C' D ((C.baseOverlapCover C').f i)) := by
  exact AffineOpenCoverCommonRefinement.compatible_of_affine_refinements (C.baseOverlapCover C')
    (P := (pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))
    (Q := (pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))
    (fun f ↦ C.overlapChartLocalComparison C' D f)
    (fun f g α w ↦ C.overlapChartLocalComparison_restrict C' D f g α w)

/-- Effective affine descent comparisons glued on the entire geometric overlap. -/
def baseOverlapComparison :
    (pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D) ≅
      (pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D) :=
  AffineOpenCoverCommonRefinement.comparisonIso (C.baseOverlapCover C')
    (P := (pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))
    (Q := (pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))
    (fun f ↦ C.overlapChartLocalComparison C' D f)
    (fun f g α w ↦ C.overlapChartLocalComparison_restrict C' D f g α w)
    (fun _ ↦ inferInstance)

/-- The glued comparison recovers the original local affine comparison exactly. -/
theorem baseOverlapComparison_restrict (i : (C.baseOverlapCover C').I₀) :
    (pullback ((C.baseOverlapCover C').f i)).map (C.baseOverlapComparison C' D).hom =
      C.baseOverlapLocalComparison C' D i :=
  AffineOpenCoverCommonRefinement.comparisonIso_restrict (C.baseOverlapCover C')
    (P := (pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))
    (Q := (pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))
    (fun f ↦ C.overlapChartLocalComparison C' D f)
    (fun f g α w ↦ C.overlapChartLocalComparison_restrict C' D f g α w)
    (fun _ ↦ inferInstance) i

end FLT.Mazur.SchemeAffineDescent.Chart
