/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Module scalar extension across a ring pushout

The pushout identifies extension from the lower ring with extension from the
upper ring followed by restriction. The comparison retains the pure tensors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.PushoutModuleScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C D : CommRingCat.{u}} (f : A ⟶ C) (g : A ⟶ B)
  (p : C ⟶ D) (q : B ⟶ D) (h : IsPushout f g p q) (M : ModuleCat C)

/-- The scalar-extension comparison of modules associated to a ring pushout. -/
def scalarIso :
    (ModuleCat.extendScalars g.hom).obj ((ModuleCat.restrictScalars f.hom).obj M) ≅
      (ModuleCat.restrictScalars q.hom).obj ((ModuleCat.extendScalars p.hom).obj M) := by
  let : Algebra A C := f.hom.toAlgebra
  let : Algebra A B := g.hom.toAlgebra
  let : Algebra C D := p.hom.toAlgebra
  let : Algebra B D := q.hom.toAlgebra
  let : Algebra A D := (f ≫ p).hom.toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  let : Module A M := Module.compHom M f.hom
  let : IsScalarTower A C M := IsScalarTower.of_compHom A C M
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.mp h.flip
  exact (Algebra.IsPushout.cancelBaseChange A B C D M).symm.toModuleIso

/-- The ring pushout comparison applies the second structural map to the tensor scalar. -/
lemma scalarIso_tmul (b : B) (m : M) :
    (scalarIso f g p q h M).hom (b ⊗ₜ[A,g.hom] m) = q b ⊗ₜ[C,p.hom] m := by
  let : Algebra A C := f.hom.toAlgebra
  let : Algebra A B := g.hom.toAlgebra
  let : Algebra C D := p.hom.toAlgebra
  let : Algebra B D := q.hom.toAlgebra
  let : Algebra A D := (f ≫ p).hom.toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  let : Module A M := Module.compHom M f.hom
  let : IsScalarTower A C M := IsScalarTower.of_compHom A C M
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.mp h.flip
  exact Algebra.IsPushout.cancelBaseChange_symm_tmul A B C D M b m

end FLT.Mazur.PushoutModuleScalars
