/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import FLT.Mazur.UniversallyDistinctSections

/-!
# Distinct original sections as actual faithful parameters

The universal section distinctness used to reconstruct cyclic subgroups is
exactly the universal faithfulness required by the actual marking open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A] (φ : A →* (𝟙_ (Over S) ⟶ E))

omit [IsSeparated E.hom] in
/-- The two universal marking predicates agree on the original sections. -/
theorem faithful_iff_distinct :
    UniversallyFaithful E A (liftMarking E A φ) ↔
      UniversallyDistinctSections.UniversallyDistinct (fun a ↦ φ a) := by
  constructor <;> intro h V g hV a b hab <;> apply h V g hV
  · change (g ≫ liftMarking E A φ) ≫ value E A a =
      (g ≫ liftMarking E A φ) ≫ value E A b
    simpa only [Category.assoc, liftMarking_value] using hab
  · change (g ≫ liftMarking E A φ) ≫ value E A a =
      (g ≫ liftMarking E A φ) ≫ value E A b at hab
    simpa only [Category.assoc, liftMarking_value] using hab

/-- Original universally distinct sections determine an actual faithful marking parameter. -/
def distinctSectionParameter
    (hφ : UniversallyDistinctSections.UniversallyDistinct (fun a ↦ φ a)) :
    𝟙_ (Over S) ⟶ faithfulScheme E A :=
  faithfulLift E A (liftMarking E A φ) ((faithful_iff_distinct E A φ).mpr hφ)

/-- Evaluation at every label returns its specified original section. -/
@[reassoc] theorem distinctSectionParameter_value
    (hφ : UniversallyDistinctSections.UniversallyDistinct (fun a ↦ φ a)) (a : A) :
    distinctSectionParameter E A φ hφ ≫ faithfulInclusion E A ≫ value E A a = φ a := by
  rw [← Category.assoc, distinctSectionParameter, faithfulLift_inclusion, liftMarking_value]

end FLT.Mazur.AuxiliaryLevel
