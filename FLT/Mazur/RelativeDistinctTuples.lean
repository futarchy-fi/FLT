/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeTupleCollision
public import FLT.Mazur.FiniteGroupOpenRestriction

/-!
# The open scheme of ordered distinct relative points

Remove every collision equalizer for unequal labels. The finite permutation
action preserves this actual open subscheme of the full relative product.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [IsSeparated E.hom] (I : Type) [Fintype I]

/-- The finite intersection of complements of all unequal-coordinate collision loci. -/
def distinctOpen : (tuples E I).left.Opens :=
  ⟨⋂ a : {a : I × I // a.1 ≠ a.2}, (collisionLocus E I a.val.1 a.val.2)ᶜ,
    isOpen_iInter_of_finite fun a ↦ (collisionLocus_isClosed E I a.val.1 a.val.2).isOpen_compl⟩

/-- Membership excludes every scheme-theoretic collision. -/
theorem mem_distinctOpen (x : (tuples E I).left) :
    x ∈ distinctOpen E I ↔ ∀ i j : I, i ≠ j → x ∉ collisionLocus E I i j := by
  simp only [distinctOpen, TopologicalSpace.Opens.mem_mk, Set.mem_iInter,
    Set.mem_compl_iff, Subtype.forall, Prod.forall]

/-- The permutation action preserves the full distinct-tuple open. -/
theorem distinctOpen_stable (e : Equiv.Perm I) :
    (schemeAction E I e).hom ⁻¹ᵁ distinctOpen E I = distinctOpen E I := by
  ext x
  change (schemeAction E I e).hom x ∈ distinctOpen E I ↔ x ∈ distinctOpen E I
  rw [mem_distinctOpen, mem_distinctOpen]
  have h (i j : I) : (schemeAction E I e).hom x ∈ collisionLocus E I i j ↔
      x ∈ collisionLocus E I (e.symm i) (e.symm j) :=
    Set.ext_iff.mp (action_preimage_collision E I e i j) x
  constructor
  · intro hx i j hij
    have he : e i ≠ e j := fun he ↦ hij (e.injective he)
    simpa only [e.symm_apply_apply] using (h (e i) (e j)).not.mp (hx (e i) (e j) he)
  · intro hx i j hij
    have he : e.symm i ≠ e.symm j := fun he ↦ hij (e.symm.injective he)
    exact (h i j).not.mpr (hx (e.symm i) (e.symm j) he)

/-- The constructed distinct-point scheme over the unchanged coefficient base. -/
def distinctScheme : Over S := Over.mk ((distinctOpen E I).ι ≫ (tuples E I).hom)

/-- The original open inclusion into all relative tuples. -/
def distinctInclusion : distinctScheme E I ⟶ tuples E I :=
  Over.homMk (distinctOpen E I).ι rfl

/-- Each original coordinate on the distinct-tuple scheme. -/
def distinctCoordinate (i : I) : distinctScheme E I ⟶ E :=
  distinctInclusion E I ≫ coordinate E I i

/-- The actual permutation action on the constructed open scheme. -/
def distinctAction : Equiv.Perm I →* Aut (distinctScheme E I).left :=
  FiniteGroupRestriction.restrictedAction (schemeAction E I)
    (distinctOpen E I) (distinctOpen_stable E I)

/-- Restriction preserves the original ambient action. -/
@[reassoc] theorem distinctAction_inclusion (e : Equiv.Perm I) :
    (distinctAction E I e).hom ≫ (distinctInclusion E I).left =
      (distinctInclusion E I).left ≫ (schemeAction E I e).hom :=
  FiniteGroupRestriction.restrictedAction_hom_ι _ _ _ e

/-- Permuting the tuple preserves its original coefficient map. -/
@[reassoc] theorem distinctAction_base (e : Equiv.Perm I) :
    (distinctAction E I e).hom ≫ (distinctScheme E I).hom =
      (distinctScheme E I).hom := by
  change _ ≫ (distinctInclusion E I).left ≫ (tuples E I).hom = _
  rw [← Category.assoc, distinctAction_inclusion, Category.assoc, schemeAction_base]
  rfl

/-- The restricted action permutes the original coordinate maps. -/
@[reassoc] theorem distinctAction_coordinate (e : Equiv.Perm I) (i : I) :
    (distinctAction E I e).hom ≫ (distinctCoordinate E I i).left =
      (distinctCoordinate E I (e.symm i)).left := by
  change _ ≫ (distinctInclusion E I).left ≫ (coordinate E I i).left = _
  rw [← Category.assoc, distinctAction_inclusion, Category.assoc]
  have h := congrArg Over.Hom.left (action_coordinate E I e i)
  change (schemeAction E I e).hom ≫ (coordinate E I i).left =
    (coordinate E I (e.symm i)).left at h
  rw [h]
  rfl

/-- Distinct labels remain distinct as original maps on every nonempty test scheme. -/
theorem distinctCoordinate_injective {T : Over S} (a : T ⟶ distinctScheme E I)
    [Nonempty T.left] : Function.Injective (fun i ↦ a ≫ distinctCoordinate E I i) := by
  intro i j hij
  by_contra hne
  let x : T.left := Classical.choice ‹Nonempty T.left›
  let b := a ≫ distinctInclusion E I
  have he : b ≫ coordinate E I i = b ≫ coordinate E I j := hij
  let z : T ⟶ collision E I i j := equalizer.lift b he
  have hz : (collisionInclusion E I i j).left (z.left x) = b.left x :=
    congrArg (fun m : T ⟶ tuples E I ↦ m.left x) (equalizer.lift_ι b he)
  have hx : b.left x ∈ distinctOpen E I := (a.left x).property
  exact (mem_distinctOpen E I _).mp hx i j hne ⟨z.left x, hz⟩

end FLT.Mazur.RelativeOrderedTuples
