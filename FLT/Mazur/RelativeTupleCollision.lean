/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeOrderedTuples

/-!
# Scheme-theoretic collisions in relative tuples

Equalizers detect equality of the original coordinate morphisms, including
residue-field data. Permutations transport these closed loci isomorphically.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) (I : Type) [Fintype I]

/-- The actual equality scheme of two coordinate maps. -/
def collision (i j : I) : Over S := equalizer (coordinate E I i) (coordinate E I j)

/-- Inclusion of the complete equality scheme. -/
def collisionInclusion (i j : I) : collision E I i j ⟶ tuples E I := equalizer.ι _ _

/-- Both original coordinates agree on the collision scheme. -/
@[reassoc] theorem collision_condition (i j : I) :
    collisionInclusion E I i j ≫ coordinate E I i =
      collisionInclusion E I i j ≫ coordinate E I j := equalizer.condition _ _

/-- The collision locus retains the scheme equalizer rather than pointwise equality. -/
def collisionLocus (i j : I) : Set (tuples E I).left :=
  Set.range (collisionInclusion E I i j).left

/-- Separatedness over the original base makes every collision closed. -/
theorem collisionLocus_isClosed [IsSeparated E.hom] (i j : I) :
    IsClosed (collisionLocus E I i j) := by
  let _ : IsClosedImmersion (collisionInclusion E I i j).left :=
    isClosedImmersion_equalizer_ι_left _ _
  exact (IsClosedImmersion.isClosedEmbedding (collisionInclusion E I i j).left).isClosed_range

/-- Relabeling transports the entire collision scheme. -/
def collisionRelabelIso (e : Equiv.Perm I) (i j : I) :
    collision E I (e.symm i) (e.symm j) ≅ collision E I i j where
  hom := equalizer.lift
    (collisionInclusion E I (e.symm i) (e.symm j) ≫ (relabelAction E I e).hom) (by
      rw [Category.assoc, Category.assoc, action_coordinate, action_coordinate]
      exact collision_condition E I _ _)
  inv := equalizer.lift (collisionInclusion E I i j ≫ (relabelAut E I e).inv) (by
    change _ ≫ relabel E I e ≫ coordinate E I (e.symm i) =
      _ ≫ relabel E I e ≫ coordinate E I (e.symm j)
    rw [relabel_coordinate, relabel_coordinate, e.apply_symm_apply, e.apply_symm_apply]
    exact collision_condition E I _ _)
  hom_inv_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      collisionInclusion, relabelAction, MonoidHom.coe_mk, OneHom.coe_mk,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      collisionInclusion, relabelAction, MonoidHom.coe_mk, OneHom.coe_mk,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The comparison respects the unchanged tuple inclusion. -/
@[reassoc] theorem collisionRelabelIso_hom_inclusion (e : Equiv.Perm I) (i j : I) :
    (collisionRelabelIso E I e i j).hom ≫ collisionInclusion E I i j =
      collisionInclusion E I (e.symm i) (e.symm j) ≫ (relabelAction E I e).hom :=
  equalizer.lift_ι _ _

/-- The inverse comparison respects the original inverse action. -/
@[reassoc] theorem collisionRelabelIso_inv_inclusion (e : Equiv.Perm I) (i j : I) :
    (collisionRelabelIso E I e i j).inv ≫ collisionInclusion E I (e.symm i) (e.symm j) =
      collisionInclusion E I i j ≫ (relabelAut E I e).inv := equalizer.lift_ι _ _

/-- Permutations preserve the actual collision equations, with both labels relabeled. -/
theorem action_preimage_collision (e : Equiv.Perm I) (i j : I) :
    (schemeAction E I e).hom ⁻¹' collisionLocus E I i j =
      collisionLocus E I (e.symm i) (e.symm j) := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(collisionRelabelIso E I e i j).inv.left z, ?_⟩
    have h := congrArg (fun f ↦ f.left z) (collisionRelabelIso_inv_inclusion E I e i j)
    change (collisionInclusion E I (e.symm i) (e.symm j)).left
      ((collisionRelabelIso E I e i j).inv.left z) =
      (relabelAut E I e).inv.left ((collisionInclusion E I i j).left z) at h
    rw [hz] at h
    exact h.trans (congrArg (fun f : (tuples E I).left ⟶ _ ↦ f x)
      (schemeAction E I e).hom_inv_id)
  · rintro ⟨z, rfl⟩
    refine ⟨(collisionRelabelIso E I e i j).hom.left z, ?_⟩
    exact congrArg (fun f ↦ f.left z) (collisionRelabelIso_hom_inclusion E I e i j)

end FLT.Mazur.RelativeOrderedTuples
