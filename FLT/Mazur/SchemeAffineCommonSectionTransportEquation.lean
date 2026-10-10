/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineExplicitCommonSectionMaps

/-!
# Sealing transport between common-section targets

Keep the rings in the morphism types explicit, so specializing a common
section does not convert projected rings inside module-sheaf categories.
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

variable (C' : Chart p)
variable {A : CommRingCat.{u}} (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)
variable (w : Spec.map f ≫ C.base = Spec.map g ≫ C'.base)

variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- Seal a raw transport equation between distinct common-section targets. -/
lemma commonSectionMaps_postcomp_of_raw
    (s : Spec A ⟶ Spec (C.commonCoverRing C' f g))
    (d : Spec A ⟶ Y)
    (hd : s ≫ (C.commonBaseCrossRefinement C' f g w).leftChart.cover = d)
    (d' : Spec A ⟶ Y)
    (hd' : s ≫ (C.commonBaseCrossRefinement C' f g w).rightChart.cover = d')
    (k : (pullback d).obj M ⟶ (pullback d').obj M)
    {B : (Spec A).Modules}
    (e : B ⟶ (pullback (Spec.map f)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map g)).obj (C'.sheaf D))
    (h : let ρ := C.commonBaseCrossRefinement C' f g w
      (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e ≫
          (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.leftChart.cover d hd).hom.app M ≫ k =
      (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e' ≫
          (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.rightChart.cover d' hd').hom.app M) :
    C.commonSectionLeftMap D C' f g w s d hd e ≫ k =
      C.commonSectionRightMap D C' f g w s d' hd' e' := by
  unfold commonSectionLeftMap commonSectionRightMap
  simpa only [Category.assoc] using h

end FLT.Mazur.SchemeAffineDescent.Chart
