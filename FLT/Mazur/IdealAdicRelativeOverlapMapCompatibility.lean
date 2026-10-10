/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapLocalHomRefinement
public import FLT.Mazur.ModuleSheafRefinementGluing

/-!
# Gluing maps on the concrete relative overlap cover

The common affine refinements of the original tensor charts provide the
geometric refinement covers needed to glue module sheaf morphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open AffineIteratedPullbackSections ModuleSheafOpenImmersionGluing

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U V : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart compositeIso

/-- Refinement-compatible maps on the concrete overlap charts satisfy gluing compatibility. -/
lemma relativeOverlapMaps_compatible (M N : (relativeTensorOverlap J f U V).Modules)
    (a : ∀ (W : X.affineOpens) (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1),
      (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).obj M ⟶
        (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).obj N)
    (ha : ∀ (W Z : X.affineOpens) (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1)
      (k : Z.1 ⟶ W.1),
      (pullback (relativeTensorTransition J f k)).map (a W i j) ≫
          (compositeIso (X := Spec (.of (RelativeAlgebra J f Z)))
          (Y := Spec (.of (RelativeAlgebra J f W))) (relativeTensorTransition J f k)
          (relativeTensorOverlapChart J f i j)
            (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
            (relativeTensorOverlapChart_refine J f i j k) N).hom =
        (compositeIso (X := Spec (.of (RelativeAlgebra J f Z)))
          (Y := Spec (.of (RelativeAlgebra J f W))) (relativeTensorTransition J f k)
          (relativeTensorOverlapChart J f i j)
            (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
            (relativeTensorOverlapChart_refine J f i j k) M).hom ≫
        a Z (k ≫ i) (k ≫ j)) :
    Compatible (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1} ↦
        Spec (.of (RelativeAlgebra J f W.val)))
      (fun W ↦ relativeTensorOverlapChart J f (homOfLE W.property.1) (homOfLE W.property.2))
      (fun W ↦ a W.val (homOfLE W.property.1) (homOfLE W.property.2)) := by
  let ι := {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1}
  let κ (W T : ι) := {Z : X.affineOpens // Z.1 ≤ W.val.1 ∧ Z.1 ≤ T.val.1}
  let l (W T : ι) (Z : κ W T) : Z.val.1 ⟶ W.val.1 := homOfLE Z.property.1
  let r (W T : ι) (Z : κ W T) : Z.val.1 ⟶ T.val.1 := homOfLE Z.property.2
  let i (W : ι) : W.val.1 ⟶ U.1 := homOfLE W.property.1
  let j (W : ι) : W.val.1 ⟶ V.1 := homOfLE W.property.2
  let _ (W T : ι) (Z : κ W T) : IsOpenImmersion (relativeTensorTransition J f (l W T Z)) :=
    relativeTensorTransition_isOpenImmersion J f (l W T Z)
  let _ (W T : ι) (Z : κ W T) : IsOpenImmersion (relativeTensorTransition J f (r W T Z)) :=
    relativeTensorTransition_isOpenImmersion J f (r W T Z)
  apply ModuleSheafMorphismGluing.compatible_of_refinement_covers
    (fun W : ι ↦ (relativeTensorOverlapChart J f (i W) (j W)).opensRange)
    (fun W ↦ ModuleSheafOpenImmersionLocalHom.localHom
      (relativeTensorOverlapChart J f (i W) (j W)) (a W.val (i W) (j W))) κ
    (fun W T Z ↦
      (relativeTensorOverlapChart J f (l W T Z ≫ i W) (l W T Z ≫ j W)).opensRange)
    (fun W T Z ↦ ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
      (relativeTensorOverlapChart J f (i W) (j W))
      (relativeTensorTransition J f (l W T Z)) _
      (relativeTensorOverlapChart_refine J f (i W) (j W) (l W T Z)))
    (fun W T Z ↦ ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
      (relativeTensorOverlapChart J f (i T) (j T))
      (relativeTensorTransition J f (r W T Z)) _
      ((relativeTensorOverlapChart_common_refinement J f
        (i T) (j T) (i W) (j W) (r W T Z) (l W T Z)).trans
        (relativeTensorOverlapChart_refine J f (i W) (j W) (l W T Z)))) ?_ ?_
  · intro W T x hx
    obtain ⟨Z, k, m, hz⟩ := relativeTensorOverlapChart_exists_refinement J f
      (i W) (j W) (i T) (j T) x hx.1 hx.2
    exact ⟨⟨Z, leOfHom k, leOfHom m⟩, hz⟩
  · intro W T Z S hS
    have hSW : S ≤ (relativeTensorOverlapChart J f (i W) (j W)).opensRange :=
      hS.trans (ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
        (relativeTensorOverlapChart J f (i W) (j W))
        (relativeTensorTransition J f (l W T Z)) _
        (relativeTensorOverlapChart_refine J f (i W) (j W) (l W T Z)))
    have hST : S ≤ (relativeTensorOverlapChart J f (i T) (j T)).opensRange :=
      hS.trans (ModuleSheafOpenImmersionLocalHom.refinementRange_le_of_eq
        (relativeTensorOverlapChart J f (i T) (j T))
        (relativeTensorTransition J f (r W T Z)) _
        (relativeTensorOverlapChart_refine J f (i T) (j T) (r W T Z)))
    have hl := relativeOverlapLocalHom_refine J f U V (i W) (j W) (l W T Z) M N
      (a W.val (i W) (j W)) (a Z.val (l W T Z ≫ i W) (l W T Z ≫ j W))
      (ha W.val Z.val (i W) (j W) (l W T Z)) S hS hSW
    have hr := relativeOverlapLocalHom_refine J f U V (i T) (j T) (r W T Z) M N
      (a T.val (i T) (j T)) (a Z.val (r W T Z ≫ i T) (r W T Z ≫ j T))
      (ha T.val Z.val (i T) (j T) (r W T Z)) S hS hST
    exact hl.symm.trans hr

end FLT.Mazur.IdealAdicGradedPullback
