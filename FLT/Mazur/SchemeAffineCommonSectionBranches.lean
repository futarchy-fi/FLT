/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossSectionMaps
public import FLT.Mazur.SchemeAffineCommonBaseCover

/-!
# Common-cover branch maps in explicit coordinates

Identify each sealed section branch with its raw common-cover composite
before specializing the sheaf and reconstruction maps.
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

/-- The left sealed map agrees with the raw common-cover section composite. -/
lemma commonSectionLeftMap_eq
    (s : Spec A ⟶ Spec (C.commonCoverRing C' f g))
    (d : Spec A ⟶ Y)
    (hd : s ≫ (C.commonBaseCrossRefinement C' f g w).leftChart.cover = d)
    {B : (Spec A).Modules}
    (e : B ⟶ (pullback (Spec.map f)).obj (C.sheaf D)) :
    let ρ := C.commonBaseCrossRefinement C' f g w
    ρ.sectionLeftMap D s d hd e =
      (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e ≫
          (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.leftChart.cover d hd).hom.app M := by
  unfold CrossRefinement.sectionLeftMap
  convert rfl using 20

variable [hqc' : ((pullback C'.cover).obj M).IsQuasicoherent]

omit [((pullback C.cover).obj M).IsQuasicoherent] in
/-- The right sealed map agrees with the raw common-cover section composite. -/
lemma commonSectionRightMap_eq
    (s : Spec A ⟶ Spec (C.commonCoverRing C' f g))
    (d : Spec A ⟶ Y)
    (hd : s ≫ (C.commonBaseCrossRefinement C' f g w).rightChart.cover = d)
    {B : (Spec A).Modules}
    (e : B ⟶ (pullback (Spec.map g)).obj (C'.sheaf D)) :
    let ρ := C.commonBaseCrossRefinement C' f g w
    ρ.sectionRightMap D s d hd e =
      (pullback s).map
        ((pullback (Spec.map ρ.ringMap)).map e ≫
          (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom) ≫
        (SheafPullbackPathComparison.comparison s ρ.rightChart.cover d hd).hom.app M := by
  unfold CrossRefinement.sectionRightMap
  convert rfl using 20

end FLT.Mazur.SchemeAffineDescent.Chart
