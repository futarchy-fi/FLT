/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDistinctTupleLift

/-!
# Singleton frames on arbitrary coefficient schemes

A single original coordinate has no collision conditions. It therefore
constructs a frame over any test scheme, with its full structure sheaf.
The singleton-frame scheme is isomorphic to the original relative scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [IsSeparated E.hom]

/-- Every singleton tuple avoids all unequal-label collisions. -/
theorem singleton_distinctOpen : distinctOpen E (Fin 1) = ⊤ := by
  apply top_unique
  intro z _
  apply (mem_distinctOpen E (Fin 1) z).mpr
  exact fun i j hij ↦ (hij (Subsingleton.elim i j)).elim

/-- The full singleton frame associated to one original coordinate. -/
def singletonFrame {T : Over S} (a : T ⟶ E) : T ⟶ distinctScheme E (Fin 1) := by
  let u := lift E (Fin 1) (fun _ ↦ a)
  have hu : Set.range u.left ⊆ Set.range (distinctOpen E (Fin 1)).ι := by
    rw [Scheme.Opens.range_ι, singleton_distinctOpen]
    exact Set.subset_univ _
  refine Over.homMk (IsOpenImmersion.lift _ u.left hu) ?_
  change _ ≫ (distinctOpen E (Fin 1)).ι ≫ (tuples E (Fin 1)).hom = T.hom
  rw [← Category.assoc, IsOpenImmersion.lift_fac]
  exact u.w

/-- The constructed frame retains the whole original tuple. -/
@[reassoc] theorem singletonFrame_inclusion {T : Over S} (a : T ⟶ E) :
    singletonFrame E a ≫ distinctInclusion E (Fin 1) = lift E (Fin 1) (fun _ ↦ a) := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- The singleton coordinate is exactly the supplied original morphism. -/
@[reassoc (attr := simp)] theorem singletonFrame_coordinate {T : Over S} (a : T ⟶ E)
    (i : Fin 1) : singletonFrame E a ≫ distinctCoordinate E (Fin 1) i = a := by
  rw [distinctCoordinate, ← Category.assoc, singletonFrame_inclusion, lift_coordinate]

/-- Singleton frames recover the original relative scheme, including nilpotents. -/
def singletonFrameIso : E ≅ distinctScheme E (Fin 1) where
  hom := singletonFrame E (𝟙 E)
  inv := distinctCoordinate E (Fin 1) 0
  hom_inv_id := singletonFrame_coordinate E (𝟙 E) 0
  inv_hom_id := by
    apply distinct_hom_ext
    intro i
    simp only [Category.assoc, singletonFrame_coordinate, Category.comp_id, Category.id_comp]
    exact congrArg (distinctCoordinate E (Fin 1)) (Subsingleton.elim 0 i)

end FLT.Mazur.RelativeOrderedTuples
