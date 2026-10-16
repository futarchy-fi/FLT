/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeUniversalDistinctLift

/-!
# Selecting distinct subframes on arbitrary schemes

An embedding of finite label types selects an actual distinct frame, with no
completeness hypothesis. Selection commutes with arbitrary tests and composition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [IsSeparated E.hom]
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H]

/-- Select any injectively indexed subtuple of the universal distinct tuple. -/
def subframe (ι : J ↪ I) : distinctScheme E I ⟶ distinctScheme E J :=
  universalDistinctLift E J (fun j ↦ distinctCoordinate E I (ι j)) (by
    intro U z hU
    let _ := hU
    exact (distinctCoordinate_injective E I z).comp ι.injective)

/-- Subframe selection retains the selected original coordinate as a morphism. -/
@[reassoc (attr := simp)] theorem subframe_coordinate (ι : J ↪ I) (j : J) :
    subframe E ι ≫ distinctCoordinate E J j = distinctCoordinate E I (ι j) :=
  universalDistinctLift_coordinate E J _ _ j

/-- Successive selections are exactly selection by the composite embedding. -/
theorem subframe_comp (ι : J ↪ I) (κ : H ↪ J) :
    subframe E ι ≫ subframe E κ = subframe E (κ.trans ι) := by
  apply distinct_hom_ext E H
  intro j
  simp only [Category.assoc, subframe_coordinate, Function.Embedding.trans_apply]

/-- Selecting every label in its original position is the identity scheme map. -/
theorem subframe_refl : subframe E (Function.Embedding.refl I) = 𝟙 _ := by
  apply distinct_hom_ext E I
  intro i
  rw [subframe_coordinate, Category.id_comp]
  rfl

/-- Selection commutes with pullback to any test scheme. -/
@[reassoc] theorem test_subframe_coordinate {T : Over S}
    (a : T ⟶ distinctScheme E I) (ι : J ↪ I) (j : J) :
    (a ≫ subframe E ι) ≫ distinctCoordinate E J j =
      a ≫ distinctCoordinate E I (ι j) := by
  rw [Category.assoc, subframe_coordinate]

end FLT.Mazur.RelativeOrderedTuples
