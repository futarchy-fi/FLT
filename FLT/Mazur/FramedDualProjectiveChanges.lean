/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FramedDualProjectivePullback

/-!
# Frame independence of geometric projective base change

Changing either actual ambient frame commutes with the geometric map. The
coordinate transformations are derived from the original sheaf isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FramedDualProjectivePullback
open ProjectiveSpace DualFreeSheafCoordinates FiniteFreePullbackFrame
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {M : Y.Modules} {ι κ ν : Type u} [Finite ι] [Finite κ] [Finite ν]
variable (e : M ≅ SheafOfModules.free ι)
variable (d : (pullback f).obj M ≅ SheafOfModules.free κ)

omit [IsAffine Y] in
/-- Changing the actual source frame preserves the constructed projective map. -/
lemma map_change_source (c : (pullback f).obj M ≅ SheafOfModules.free ν) :
    (projectiveIso (d.symm ≪≫ c)).hom ≫ map f e c = map f e d := by
  have h : (d.symm ≪≫ c) ≪≫ (c.symm ≪≫ frame f e) = d.symm ≪≫ frame f e := by
    apply Iso.ext
    simp
  rw [map, map, ← Category.assoc, ← Iso.trans_hom, ← projectiveIso_trans, h]

/-- Changing the original target frame gives the corresponding dual projective change. -/
lemma map_change_target (c : M ≅ SheafOfModules.free ν) :
    map f e d ≫ (projectiveIso (e.symm ≪≫ c)).hom = map f c d := by
  have h : (d.symm ≪≫ frame f e) ≪≫
      AffineFreeSheafCoordinates.pullbackFreeIso f (e.symm ≪≫ c) =
        d.symm ≪≫ frame f c := by
    rw [← change_frame]
    apply Iso.ext
    simp
  rw [map, map, Category.assoc, projectiveIso_pullback,
    ← Category.assoc, ← Iso.trans_hom, ← projectiveIso_trans, h]

end FLT.Mazur.FramedDualProjectivePullback
