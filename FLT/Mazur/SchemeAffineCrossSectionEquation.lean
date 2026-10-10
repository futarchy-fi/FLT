/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossSectionMaps

/-!
# Raw comparison for sealed section maps

Name the section composites before specializing the common rings. The
comparison reuses the proved cross-refinement cancellation with small
morphism types at its geometric application sites.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
attribute [local irreducible] sheaf refinementReconstruction reconstruction

namespace CrossRefinement
variable {C} {C' : Chart p} (ρ : C.CrossRefinement C')

variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- Raw reconstruction comparison gives equality of the sealed section maps. -/
lemma sectionMaps_eq
    (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.leftChart.cover = d)
    (hd' : s ≫ ρ.rightChart.cover = d)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D))
    (h : (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e ≫
          (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.leftChart.cover d hd).hom.app M =
      (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e' ≫
          (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.rightChart.cover d hd').hom.app M) :
    ρ.sectionLeftMap D s d hd e = ρ.sectionRightMap D s d hd' e' := by
  unfold sectionLeftMap sectionRightMap
  exact h

end CrossRefinement
end FLT.Mazur.SchemeAffineDescent.Chart
