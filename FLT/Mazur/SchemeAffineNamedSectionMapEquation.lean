/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineNamedCrossSectionMaps

/-!
# Named section composites and sealed maps

Equations of raw section composites give equations of the sealed maps.
The conversion is checked with independently named rings.
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
variable (A T : CommRingCat.{u}) (φ : A ⟶ T) (hφ : φ.hom.FaithfullyFlat)
variable (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)
variable (b : C.coverRing ⟶ T) (c : C'.coverRing ⟶ T)
variable (hb : C.ringMap ≫ b = f ≫ φ) (hc : C'.ringMap ≫ c = g ≫ φ)
variable (w : Spec.map f ≫ C.base = Spec.map g ≫ C'.base)
attribute [local irreducible] Chart.sheaf Chart.refinementReconstruction Chart.reconstruction

/-- Raw section reconstruction equations imply equality of the sealed maps. -/
lemma sectionMaps_eq_of_raw
    (s : Spec A ⟶ Spec T)
    (d : Spec A ⟶ Y) (hd : s ≫ (Spec.map b ≫ C.cover) = d)
    (hd' : s ≫ (Spec.map c ≫ C'.cover) = d)
    {B : (Spec A).Modules}
    (e : B ⟶ (pullback (Spec.map f)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map g)).obj (C'.sheaf D))
    (h : let ρ : C.CrossRefinement C' := ⟨A, T, φ, hφ, f, g, b, c, hb, hc, w⟩
      (pullback s).map
        ((pullback (Spec.map φ)).map e ≫
          (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.leftChart.cover d hd).hom.app M =
      (pullback s).map
        ((pullback (Spec.map φ)).map e' ≫
          (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.rightChart.cover d hd').hom.app M) :
    let ρ : C.CrossRefinement C' := ⟨A, T, φ, hφ, f, g, b, c, hb, hc, w⟩
    ρ.sectionLeftMap D s d hd e = ρ.sectionRightMap D s d hd' e' := by
  unfold sectionLeftMap sectionRightMap
  convert h using 20

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
