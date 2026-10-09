/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechScalars
public import FLT.Mazur.FlatStructureSectionComplex
public import FLT.Mazur.AffineCoverIntersections

/-!
# Flat terms of the bounded structure Cech complex

A finite affine cover of a separated flat family gives a bounded complex of
flat modules over its affine base. The module structures are the original
coefficient actions, restricted along the actual structural pullback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex FCurve Chow

variable {X S : Scheme} (f : X ⟶ S) [IsAffine S] [Flat f] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

/-- Increasing tuple coordinates identify the actual term with base-valued chart sections. -/
def structureTermEquiv (n : ℕ) :
    @LinearEquiv Γ(S, ⊤) Γ(S, ⊤) _ _ (RingHom.id _) (RingHom.id _) _ _
      (Term U (moduleAbelianSheaf (structureModule X)) n)
      (∀ a : Tuple (ι := ι) n,
        baseSections (structureModule X) f.appTop.hom (CechSheafHZero.V U n a.val))
      _ _ (Module.compHom _ f.appTop.hom) (Pi.module _ _ _) := by
  let _ := Module.compHom (Term U (moduleAbelianSheaf (structureModule X)) n) f.appTop.hom
  exact
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

include hU in
/-- Each actual bounded Cech term is flat over the original affine base. -/
theorem structureTerm_flat (n : ℕ) :
    let _ := Module.compHom (Term U (moduleAbelianSheaf (structureModule X)) n) f.appTop.hom
    Module.Flat Γ(S, ⊤) (Term U (moduleAbelianSheaf (structureModule X)) n) := by
  have hflat : Module.Flat Γ(S, ⊤)
      (∀ a : Tuple (ι := ι) n,
        baseSections (structureModule X) f.appTop.hom (CechSheafHZero.V U n a.val)) :=
     FlatStructureSectionComplex.chartProduct_flat f
    (fun a : Tuple (ι := ι) n ↦ CechSheafHZero.V U n a.val)
    (fun a ↦ affineCover_intersection_isAffineOpen U hU n a.val)
  let _ := Module.compHom (Term U (moduleAbelianSheaf (structureModule X)) n) f.appTop.hom
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflat (structureTermEquiv f U n)

end FLT.Mazur.IncreasingCechScalars
