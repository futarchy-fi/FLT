/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossSectionComparison

/-!
# Sealed maps for cross-refinement section comparison

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

/-- Reconstruction in the original chart after an affine base test. -/
def sectionOriginalMap {A : CommRingCat.{u}}
    (f : C.baseRing ⟶ A) (t : Spec A ⟶ Spec C.coverRing)
    (ha : t ≫ Spec.map C.ringMap = Spec.map f)
    (d : Spec A ⟶ Y) (hcd : t ≫ C.cover = d)
    {B : (Spec A).Modules} (e : B ⟶ (pullback (Spec.map f)).obj (C.sheaf D)) :
    B ⟶ (pullback d).obj M :=
  e ≫ (SheafPullbackPathComparison.comparison t (Spec.map C.ringMap)
      (Spec.map f) ha).inv.app (C.sheaf D) ≫
    (pullback t).map (C.reconstruction D).hom ≫
    (SheafPullbackPathComparison.comparison t C.cover d hcd).hom.app M

namespace CrossRefinement
variable {C} {C' : Chart p} (ρ : C.CrossRefinement C')

/-- The left reconstruction pulled back along a common-cover section. -/
def sectionLeftMap (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.leftChart.cover = d)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D)) :
    (pullback s).obj ((pullback (Spec.map ρ.ringMap)).obj B) ⟶ (pullback d).obj M :=
  (pullback s).map
      ((pullback (Spec.map ρ.ringMap)).map e ≫
        (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
      (SheafPullbackPathComparison.comparison s ρ.leftChart.cover d hd).hom.app M

variable [hqc' : ((pullback C'.cover).obj M).IsQuasicoherent]

/-- The right reconstruction pulled back along the same common-cover section. -/
def sectionRightMap (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.rightChart.cover = d)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D)) :
    (pullback s).obj ((pullback (Spec.map ρ.ringMap)).obj B) ⟶ (pullback d).obj M :=
  (pullback s).map
      ((pullback (Spec.map ρ.ringMap)).map e ≫
        (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
      (SheafPullbackPathComparison.comparison s ρ.rightChart.cover d hd).hom.app M

/-- Cancel the common section using sealed reconstruction maps. -/
lemma sectionOriginalMap_eq
    (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (hs : s ≫ Spec.map ρ.ringMap = 𝟙 (Spec ρ.baseRing))
    (t : Spec ρ.baseRing ⟶ Spec C.coverRing) (ht : s ≫ Spec.map ρ.leftCover = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map ρ.leftBase)
    (v : Spec ρ.baseRing ⟶ Spec C'.coverRing) (hv : s ≫ Spec.map ρ.rightCover = v)
    (hb : v ≫ Spec.map C'.ringMap = Spec.map ρ.rightBase)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.leftChart.cover = d)
    (hd' : s ≫ ρ.rightChart.cover = d) (hcd : t ≫ C.cover = d) (hcd' : v ≫ C'.cover = d)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D))
    (h : ρ.sectionLeftMap D s d hd e = ρ.sectionRightMap D s d hd' e') :
    C.sectionOriginalMap D ρ.leftBase t ha d hcd e =
      C'.sectionOriginalMap D ρ.rightBase v hb d hcd' e' := by
  exact section_comparison D ρ s hs t ht ha v hv hb d hd hd' hcd hcd' e e' h

end CrossRefinement
attribute [irreducible] sectionOriginalMap CrossRefinement.sectionLeftMap
  CrossRefinement.sectionRightMap
end FLT.Mazur.SchemeAffineDescent.Chart
