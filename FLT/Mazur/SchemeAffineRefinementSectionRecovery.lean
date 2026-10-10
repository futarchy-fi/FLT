/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNamedRefinementSection
public import FLT.Mazur.SchemeAffineChartReconstruction

/-!
# Affine refinement reconstruction along a section

The original chart reconstruction is recovered by restricting a refinement
along a section of its covering map. All coordinates are geometric maps;
the reconstruction equation is proved from pullback comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable (ρ : C.Refinement C')
attribute [local irreducible] sheaf reconstruction

/-- Restricting an actual affine refinement to a section retains the original reconstruction. -/
@[reassoc]
lemma refinementReconstruction_section
    (s : Spec C'.baseRing ⟶ Spec C'.coverRing)
    (hs : s ≫ Spec.map C'.ringMap = 𝟙 (Spec C'.baseRing))
    (t : Spec C'.baseRing ⟶ Spec C.coverRing) (ht : s ≫ Spec.map ρ.cover = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map ρ.base)
    (d : Spec C'.baseRing ⟶ Y) (hd : s ≫ C'.cover = d) (hcd : t ≫ C.cover = d) :
    (pullback s).map (C.refinementReconstruction C' D ρ).hom ≫
        (SheafPullbackPathComparison.comparison s C'.cover d hd).hom.app M =
      (retractIso s (Spec.map C'.ringMap) hs
          ((pullback (Spec.map ρ.base)).obj (C.sheaf D))).hom ≫
        (SheafPullbackPathComparison.comparison t (Spec.map C.ringMap) 
          (Spec.map ρ.base) ha).inv.app (C.sheaf D) ≫
        (pullback t).map (C.reconstruction D).hom ≫
        (SheafPullbackPathComparison.comparison t C.cover d hcd).hom.app M := by
  exact AffineNamedRefinementReconstruction.chart_section
    C.ringMap C'.ringMap ρ.base ρ.cover ρ.square C.cover C'.cover ρ.cover_over
    s hs t ht ha d hd hcd (C.reconstruction D)

/-- Refinement reconstruction after a base test retains that test along the section. -/
@[reassoc]
lemma refinementReconstruction_section_test
    (s : Spec C'.baseRing ⟶ Spec C'.coverRing)
    (hs : s ≫ Spec.map C'.ringMap = 𝟙 (Spec C'.baseRing))
    (t : Spec C'.baseRing ⟶ Spec C.coverRing) (ht : s ≫ Spec.map ρ.cover = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map ρ.base)
    (d : Spec C'.baseRing ⟶ Y) (hd : s ≫ C'.cover = d) (hcd : t ≫ C.cover = d)
    {B : (Spec C'.baseRing).Modules} (e : B ⟶ (pullback (Spec.map ρ.base)).obj (C.sheaf D)) :
    (pullback s).map
        ((pullback (Spec.map C'.ringMap)).map e ≫
          (C.refinementReconstruction C' D ρ).hom) ≫
        (SheafPullbackPathComparison.comparison s C'.cover d hd).hom.app M =
      (retractIso s (Spec.map C'.ringMap) hs B).hom ≫ e ≫
        (SheafPullbackPathComparison.comparison t (Spec.map C.ringMap)
          (Spec.map ρ.base) ha).inv.app (C.sheaf D) ≫
        (pullback t).map (C.reconstruction D).hom ≫
        (SheafPullbackPathComparison.comparison t C.cover d hcd).hom.app M := by
  have hn := (pullbackComp s (Spec.map C'.ringMap) ≪≫ pullbackCongr hs ≪≫
    pullbackId (Spec C'.baseRing)).hom.naturality e
  change (pullback s).map ((pullback (Spec.map C'.ringMap)).map e) ≫
      (retractIso s (Spec.map C'.ringMap) hs _).hom =
    (retractIso s (Spec.map C'.ringMap) hs B).hom ≫ e at hn
  rw [Functor.map_comp, Category.assoc,
    refinementReconstruction_section C C' D ρ s hs t ht ha d hd hcd]
  simpa only [Category.assoc] using hn =≫
    ((SheafPullbackPathComparison.comparison t (Spec.map C.ringMap)
      (Spec.map ρ.base) ha).inv.app (C.sheaf D) ≫
      (pullback t).map (C.reconstruction D).hom ≫
      (SheafPullbackPathComparison.comparison t C.cover d hcd).hom.app M)

end FLT.Mazur.SchemeAffineDescent.Chart
