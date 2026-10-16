/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Ordered tuples over the unchanged coefficient scheme

The finite product uses the entire given scheme over its base. Permutations
relabel the universal tuple and act by actual automorphisms over that base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) (I : Type) [Fintype I]

/-- All ordered tuples in the original relative scheme. -/
def tuples : Over S := ∏ᶜ fun _ : I ↦ E

/-- Each original coordinate of the universal tuple. -/
def coordinate (i : I) : tuples E I ⟶ E := Pi.π _ i

/-- Every tuple of original maps has its canonical representing map. -/
def lift {T : Over S} (a : I → (T ⟶ E)) : T ⟶ tuples E I := Pi.lift a

/-- The representing map retains each original coordinate. -/
@[reassoc (attr := simp)] theorem lift_coordinate {T : Over S}
    (a : I → (T ⟶ E)) (i : I) : lift E I a ≫ coordinate E I i = a i :=
  Pi.lift_comp_π _ _

/-- Equality of tuples is equality of every original coordinate. -/
@[ext] theorem hom_ext {T : Over S} {a b : T ⟶ tuples E I}
    (h : ∀ i, a ≫ coordinate E I i = b ≫ coordinate E I i) : a = b :=
  Pi.hom_ext _ _ h

/-- Relabeling keeps the original coefficient morphism. -/
def relabel (e : I → I) : tuples E I ⟶ tuples E I :=
  lift E I (fun i ↦ coordinate E I (e i))

/-- Relabeling acts on the actual coordinate maps. -/
@[reassoc (attr := simp)] theorem relabel_coordinate (e : I → I) (i : I) :
    relabel E I e ≫ coordinate E I i = coordinate E I (e i) := lift_coordinate E I _ i

/-- Identity relabeling gives the identity morphism. -/
@[simp] theorem relabel_id : relabel E I id = 𝟙 _ := by
  ext i
  simp

/-- Relabeling is contravariant in functions on the labels. -/
theorem relabel_comp (e f : I → I) :
    relabel E I (e ∘ f) = relabel E I e ≫ relabel E I f := by
  ext i
  simp

/-- A permutation gives an automorphism of the full relative product. -/
def relabelAut (e : Equiv.Perm I) : Aut (tuples E I) where
  hom := relabel E I e.symm
  inv := relabel E I e
  hom_inv_id := by
    apply hom_ext
    intro i
    simp only [Category.assoc, relabel_coordinate, e.symm_apply_apply, Category.id_comp]
  inv_hom_id := by
    apply hom_ext
    intro i
    simp only [Category.assoc, relabel_coordinate, e.apply_symm_apply, Category.id_comp]

/-- The permutation group acts on the original tuple scheme over its base. -/
def relabelAction : Equiv.Perm I →* Aut (tuples E I) where
  toFun := relabelAut E I
  map_one' := by
    apply Aut.ext
    exact relabel_id E I
  map_mul' e f := by
    apply Aut.ext
    change relabel E I (e * f).symm = relabel E I f.symm ≫ relabel E I e.symm
    rw [← relabel_comp]
    rfl

/-- The underlying scheme action used for geometric free-action tests. -/
def schemeAction : Equiv.Perm I →* Aut (tuples E I).left :=
  (Functor.mapAut (tuples E I) (Over.forget S)).comp (relabelAction E I)

/-- The action retains the original base morphism. -/
@[reassoc (attr := simp)] theorem schemeAction_base (e : Equiv.Perm I) :
    (schemeAction E I e).hom ≫ (tuples E I).hom = (tuples E I).hom :=
  (relabelAut E I e).hom.w

/-- The inverse convention gives a left action on scheme points. -/
@[reassoc (attr := simp)] theorem action_coordinate (e : Equiv.Perm I) (i : I) :
    (relabelAction E I e).hom ≫ coordinate E I i = coordinate E I (e.symm i) :=
  relabel_coordinate E I _ _

end FLT.Mazur.RelativeOrderedTuples
