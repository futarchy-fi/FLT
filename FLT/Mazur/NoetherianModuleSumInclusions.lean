/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianModuleSum

/-!
# Degree inclusions on all Noetherian opens

The module sum's original inclusion in each degree is sectionwise the
finitely supported single-coordinate map, on arbitrary opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped DirectSum

universe u

namespace FLT.Mazur.NoetherianModuleSum

variable {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (M : ℕ → X.Modules)

/-- The original degree inclusion as an actual module sheaf morphism. -/
def inclusion (n : ℕ) : M n ⟶ sum M :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (DirectSum.of (fun k ↦ Γ(M k, U.unop)) n)
      naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro s
        exact (DirectSum.map_of (fun k ↦ ((M k).presheaf.map f).hom) n s).symm }
    (fun U r s ↦ DirectSum.of_smul Γ(X, U.unop)
      (M := fun k ↦ Γ(M k, U.unop)) n r s)⟩

/-- The actual sheaf inclusion is the original single-coordinate map on every open. -/
lemma inclusion_app (n : ℕ) (U : X.Opens) (s : Γ(M n, U)) :
    (inclusion M n).app U s = DirectSum.of (fun k ↦ Γ(M k, U)) n s := rfl

/-- These sectionwise maps are the maps obtained from the affine universal property. -/
lemma inclusion_eq_affine (n : ℕ) :
    inclusion M n = AffineBasisSumMaps.ι M (sum M) (basisIso M)
      (fun _ _ _ ↦ rfl) n := by
  apply AffineBasisModuleMorphism.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  rw [AffineBasisSumMaps.ι_app]
  rfl

/-- The sectionwise degree map is the injection into the categorical sheaf coproduct. -/
lemma inclusion_coproductIso_hom (n : ℕ) :
    inclusion M n ≫ (coproductIso M).hom = CategoryTheory.Limits.Sigma.ι M n := by
  rw [inclusion_eq_affine]
  exact AffineBasisSumMaps.ι_coproductIso_hom M (sum M) (basisIso M) _ n

end FLT.Mazur.NoetherianModuleSum
