/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualFreeSheafCoordinates

/-!
# Geometric base change in actual finite free frames

An arbitrary frame of the pulled sheaf maps to the original framed projective
space by its dual coordinate change followed by coefficient change. The square
over the original affine morphism is cartesian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FramedDualProjectivePullback
open ProjectiveSpace DualFreeSheafCoordinates FiniteFreePullbackFrame
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {M : Y.Modules} {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : M ≅ SheafOfModules.free ι)
variable (d : (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.free κ)

/-- The actual projective morphism for the original and pulled ambient frames. -/
def map : space Γ(X, ⊤) κ ⟶ space Γ(Y, ⊤) ι :=
  (projectiveIso (d.symm ≪≫ frame f e)).hom ≫ coefficientMap f.appTop.hom ι

omit [IsAffine Y] in
/-- The canonical pulled frame gives exactly the original coefficient morphism. -/
lemma map_frame : map f e (frame f e) = coefficientMap f.appTop.hom ι := by
  simp only [map, Iso.symm_self_id, projectiveIso_refl, Iso.refl_hom, Category.id_comp]

/-- The constructed morphism lies over the given affine base morphism. -/
@[reassoc]
lemma map_projection :
    map f e d ≫ affineProjection Y ι = affineProjection X κ ≫ f := by
  rw [map, Category.assoc, coefficientMap_affineProjection,
    projectiveIso_projection_assoc]

/-- The actual framed projective square is cartesian for arbitrary base morphisms. -/
lemma map_isPullback :
    IsPullback (map f e d) (affineProjection X κ) (affineProjection Y ι) f := by
  apply (affine_isPullback f ι).of_iso
    (projectiveIso (d.symm ≪≫ frame f e)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [map]
  · change affineProjection X ι =
      (projectiveIso (d.symm ≪≫ frame f e)).inv ≫ affineProjection X κ
    rw [Iso.eq_inv_comp]
    exact projectiveIso_projection _
  · simp
  · simp

/-- In particular, pulling along an open immersion gives an open projective chart map. -/
instance [IsOpenImmersion f] : IsOpenImmersion (map f e d) :=
  IsOpenImmersion.of_isPullback (map_isPullback f e d).flip inferInstance

end FLT.Mazur.FramedDualProjectivePullback
