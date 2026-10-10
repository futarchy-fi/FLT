/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossSectionMaps

/-!
# Cancellation with distinct reconstruction targets

A morphism between the two source pullbacks may follow the left reconstruction.
Canceling the common retraction preserves this morphism, including descent transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p}
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable (ρ : C.CrossRefinement C')
attribute [local irreducible] Chart.sheaf Chart.refinementReconstruction Chart.reconstruction

/-- Cancel the common section with a morphism between distinct source pullbacks. -/
lemma section_comparison_postcomp
    (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (hs : s ≫ Spec.map ρ.ringMap = 𝟙 (Spec ρ.baseRing))
    (t : Spec ρ.baseRing ⟶ Spec C.coverRing) (ht : s ≫ Spec.map ρ.leftCover = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map ρ.leftBase)
    (v : Spec ρ.baseRing ⟶ Spec C'.coverRing) (hv : s ≫ Spec.map ρ.rightCover = v)
    (hb : v ≫ Spec.map C'.ringMap = Spec.map ρ.rightBase)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.leftChart.cover = d)
    (d' : Spec ρ.baseRing ⟶ Y) (hd' : s ≫ ρ.rightChart.cover = d')
    (hcd : t ≫ C.cover = d) (hcd' : v ≫ C'.cover = d')
    (k : (pullback d).obj M ⟶ (pullback d').obj M)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D))
    (h : (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e ≫
          (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.leftChart.cover d hd).hom.app M ≫ k =
      (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e' ≫
          (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.rightChart.cover d' hd').hom.app M) :
    e ≫ (SheafPullbackPathComparison.comparison t (Spec.map C.ringMap)
        (Spec.map ρ.leftBase) ha).inv.app (C.sheaf D) ≫
        (pullback t).map (C.reconstruction D).hom ≫
        (SheafPullbackPathComparison.comparison t C.cover d hcd).hom.app M ≫ k =
      e' ≫ (SheafPullbackPathComparison.comparison v (Spec.map C'.ringMap)
        (Spec.map ρ.rightBase) hb).inv.app (C'.sheaf D) ≫
        (pullback v).map (C'.reconstruction D).hom ≫
        (SheafPullbackPathComparison.comparison v C'.cover d' hcd').hom.app M := by
  apply (cancel_epi (retractIso s (Spec.map ρ.ringMap) hs B).hom).mp
  have hl := section_left C C' D ρ s hs t ht ha d hd hcd e
  have hr := section_right C C' D ρ s hs v hv hb d' hd' hcd' e'
  have hk := congrArg (· ≫ k) hl
  simp only [Category.assoc] at hk
  exact hk.symm.trans (h.trans hr)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
