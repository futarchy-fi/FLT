/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreePullbackFrame
public import FLT.Mazur.FiniteFreeDualProjectiveTransitions
public import FLT.Mazur.ProjectiveSpaceAffineBase

/-!
# Dual projective changes of actual free sheaves

The dual projective change attached to a sheaf isomorphism respects composition
and arbitrary affine pullback. These laws apply to frames of pulled ambient sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualFreeSheafCoordinates
open AffineFreeSheafCoordinates ProjectiveSpace
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
variable {ι κ ν : Type u} [Finite ι] [Finite κ] [Finite ν]

/-- The dual projective isomorphism of an actual affine free-sheaf isomorphism. -/
def projectiveIso (e : (SheafOfModules.free ι : X.Modules) ≅ SheafOfModules.free κ) :
    space Γ(X, ⊤) ι ≅ space Γ(X, ⊤) κ :=
  linearIso (FiniteFreeContragredient.map (coordinates X e))

/-- The identity sheaf change gives the identity projective change. -/
lemma projectiveIso_refl :
    projectiveIso (Iso.refl (SheafOfModules.free ι : X.Modules)) = Iso.refl _ := by
  rw [projectiveIso, coordinates_refl, FiniteFreeContragredient.map_refl, linearIso_refl]

/-- Projective changes compose in the same order as the original sheaf changes. -/
lemma projectiveIso_trans
    (e : (SheafOfModules.free ι : X.Modules) ≅ SheafOfModules.free κ)
    (d : (SheafOfModules.free κ : X.Modules) ≅ SheafOfModules.free ν) :
    projectiveIso (e ≪≫ d) = projectiveIso e ≪≫ projectiveIso d := by
  rw [projectiveIso, coordinates_trans, ← FiniteFreeContragredient.map_trans,
    ← linearIso_trans]
  rfl

/-- The dual free-sheaf change preserves the actual affine projection. -/
@[reassoc]
lemma projectiveIso_projection
    (e : (SheafOfModules.free ι : X.Modules) ≅ SheafOfModules.free κ) :
    (projectiveIso e).hom ≫ affineProjection X κ = affineProjection X ι :=
  linearIso_affineProjection X _

/-- The actual dual coordinate change commutes with arbitrary affine coefficient change. -/
@[reassoc]
lemma projectiveIso_pullback (f : X ⟶ Y)
    (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ) :
    coefficientMap f.appTop.hom ι ≫ (projectiveIso e).hom =
      (projectiveIso (pullbackFreeIso f e)).hom ≫ coefficientMap f.appTop.hom κ :=
  FiniteFreeContragredient.projective_coefficient _ _ _ (coordinates_pullback f e)

end FLT.Mazur.DualFreeSheafCoordinates
