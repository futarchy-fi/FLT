/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Injective field markings give points of the faithful open

An injective marking over a field stays injective on every nonempty test:
the test map to the field is flat and surjective, hence an epimorphism.
Thus field-valued bases give actual maps into the constructed faithful open.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryLevel

variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A]
  {K : Type} [Field K] (g : Spec (.of K) ⟶ S)
  (φ : A →* (Over.mk g ⟶ E)) (hφ : Function.Injective φ)

include hφ

omit [IsSeparated E.hom] in
/-- Ordinary injectivity over a field implies universal faithfulness. -/
theorem fieldMarking_universallyFaithful :
    UniversallyFaithful E A (liftMarking E A φ) := by
  intro V f hV
  let _ := hV
  let t : V.left ⟶ Spec (.of K) := f.left
  have : Surjective t := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi t := Flat.epi_of_flat_of_surjective t
  intro a b hab
  apply hφ
  apply Over.OverMorphism.ext
  apply (cancel_epi t).mp
  change (f ≫ liftMarking E A φ) ≫ value E A a =
    (f ≫ liftMarking E A φ) ≫ value E A b at hab
  rw [Category.assoc, Category.assoc, liftMarking_value, liftMarking_value] at hab
  exact congrArg Over.Hom.left hab

/-- An injective field marking supplies an actual point of the faithful level scheme. -/
def fieldFaithfulLift : Over.mk g ⟶ faithfulScheme E A :=
  faithfulLift E A (liftMarking E A φ) (fieldMarking_universallyFaithful E A g φ hφ)

/-- The lift retains the original field-valued marking. -/
@[reassoc (attr := simp)] theorem fieldFaithfulLift_value (a : A) :
    fieldFaithfulLift E A g φ hφ ≫ faithfulInclusion E A ≫ value E A a = φ a := by
  rw [← Category.assoc, fieldFaithfulLift, faithfulLift_inclusion, liftMarking_value]

end FLT.Mazur.AuxiliaryLevel
