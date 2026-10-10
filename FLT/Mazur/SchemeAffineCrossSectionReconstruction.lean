/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinement
public import FLT.Mazur.SchemeAffineRefinementSectionRecovery

/-!
# Section normalization for abstract cross refinements

Both branches of a cross refinement recover the original chart coordinates
along a section. Explicit congruence isolates the chart projections before
Lean compares the dependent pullback types.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [hqc : ((pullback C.cover).obj M).IsQuasicoherent]
variable [hqc' : ((pullback C'.cover).obj M).IsQuasicoherent]
variable (ρ : C.CrossRefinement C')
attribute [local irreducible] Chart.sheaf Chart.refinementReconstruction Chart.reconstruction

omit hqc' in
/-- The left cross-refinement section preserves any preceding base-chart map. -/
lemma Chart.CrossRefinement.section_left
    (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (hs : s ≫ Spec.map ρ.ringMap = 𝟙 (Spec ρ.baseRing))
    (t : Spec ρ.baseRing ⟶ Spec C.coverRing) (ht : s ≫ Spec.map ρ.leftCover = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map ρ.leftBase)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.leftChart.cover = d)
    (hcd : t ≫ C.cover = d)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D)) :
    (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e ≫
          (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.leftChart.cover d hd).hom.app M =
      (retractIso s (Spec.map ρ.ringMap) hs B).hom ≫ e ≫
        (SheafPullbackPathComparison.comparison t (Spec.map C.ringMap)
          (Spec.map ρ.leftBase) ha).inv.app (C.sheaf D) ≫
        (pullback t).map (C.reconstruction D).hom ≫
        (SheafPullbackPathComparison.comparison t C.cover d hcd).hom.app M := by
  have h := @Chart.refinementReconstruction_section_test.{u} X Y p C ρ.leftChart M D hqc
    ρ.leftRefinement s hs t ht ha d hd hcd B e
  convert h using 20 <;> rfl

omit hqc in
/-- The right cross-refinement section preserves any preceding base-chart map. -/
lemma Chart.CrossRefinement.section_right
    (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (hs : s ≫ Spec.map ρ.ringMap = 𝟙 (Spec ρ.baseRing))
    (t : Spec ρ.baseRing ⟶ Spec C'.coverRing) (ht : s ≫ Spec.map ρ.rightCover = t)
    (ha : t ≫ Spec.map C'.ringMap = Spec.map ρ.rightBase)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.rightChart.cover = d)
    (hcd : t ≫ C'.cover = d)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D)) :
    (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e ≫
          (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.rightChart.cover d hd).hom.app M =
      (retractIso s (Spec.map ρ.ringMap) hs B).hom ≫ e ≫
        (SheafPullbackPathComparison.comparison t (Spec.map C'.ringMap)
          (Spec.map ρ.rightBase) ha).inv.app (C'.sheaf D) ≫
        (pullback t).map (C'.reconstruction D).hom ≫
        (SheafPullbackPathComparison.comparison t C'.cover d hcd).hom.app M := by
  have h := @Chart.refinementReconstruction_section_test.{u} X Y p C' ρ.rightChart M D hqc'
    ρ.rightRefinement s hs t ht ha d hd hcd B e
  convert h using 20 <;> rfl

end FLT.Mazur.SchemeAffineDescent
