/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FramedDualProjectiveChanges
public import FLT.Mazur.ProjectiveCoefficientFunctor

/-!
# Composition of geometric framed projective maps

Successive base changes compose through the actual sheaf pullback comparison,
with arbitrary choices of finite free frames at both intermediate stages.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FramedDualProjectivePullback
open ProjectiveSpace DualFreeSheafCoordinates FiniteFreePullbackFrame
open AffineFreeSheafCoordinates
variable {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable {M : Z.Modules} {ι κ ν : Type u} [Finite ι] [Finite κ] [Finite ν]
variable (e : M ≅ SheafOfModules.free ι)
variable (c : (pullback g).obj M ≅ SheafOfModules.free κ)
variable (d : (pullback f).obj ((pullback g).obj M) ≅ SheafOfModules.free ν)

/-- Composing the constructed maps preserves the original geometric pullback comparison. -/
lemma map_comp :
    map f c d ≫ map g e c =
      map (f ≫ g) e ((pullbackComp f g).symm.app M ≪≫ d) := by
  have h : (d.symm ≪≫ frame f c) ≪≫ pullbackFreeIso f (c.symm ≪≫ frame g e) =
      ((pullbackComp f g).symm.app M ≪≫ d).symm ≪≫ frame (f ≫ g) e := by
    rw [← change_frame]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun k ↦ d.inv ≫ k) (congrArg Iso.hom (frame_comp f g e)).symm
  simp only [map, Category.assoc]
  rw [projectiveIso_pullback_assoc]
  rw [← Category.assoc (projectiveIso (d.symm ≪≫ frame f c)).hom,
    ← Iso.trans_hom, ← projectiveIso_trans, h, coefficientMap_appTop_comp]

end FLT.Mazur.FramedDualProjectivePullback
