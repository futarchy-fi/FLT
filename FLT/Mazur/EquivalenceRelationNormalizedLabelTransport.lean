/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedLabelChange
public import FLT.Mazur.EquivalenceRelationNormalizedActionComplete

/-!
# Label transport preserves the action and completeness

The label isomorphisms intertwine the moving permutation actions and preserve
whole-fiber completeness. These are exact scheme and geometric-frame statements;
they do not assert that the complete locus is open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)

/-- Changing the distinguished label commutes with every moving permutation. -/
@[reassoc] theorem labelChange_action (σ : Equiv.Perm I) :
    labelChange e I o o' ≫ (action e I o' σ).hom =
      (action e I o σ).hom ≫ labelChange e I o o' := by
  apply hom_ext_second p q I o' e
  intro i
  change (labelChange e I o o' ≫ actionMap e I o' σ) ≫ _ ≫ q =
    (actionMap e I o σ ≫ labelChange e I o o') ≫ _ ≫ q
  simp only [Category.assoc, actionMap_second, labelChange_second]

local instance labelCompleteOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local notation "E" => Over.mk p
variable {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)

/-- The transported test frame is rebased along the actual original label arrow. -/
theorem testFrame_labelChange :
    testFrame I o' (u ≫ labelChange e I o o') =
      frameCast I (by simp only [Category.assoc, labelChange_first])
        (comparisonFrame e I o u (u ≫ coordinate p q I o o')
          (by rw [Category.assoc, coordinate_first])) := by
  apply frame_ext_second e I
  intro i
  change (testFrame I o' (u ≫ labelChange e I o o') ≫
    distinctCoordinate E I i).left ≫ q =
      (rebaseFrame e I (u ≫ coordinate p q I o o') _ ≫
        distinctCoordinate E I i).left ≫ q
  rw [rebaseFrame_second]
  change ((u ≫ labelChange e I o o') ≫ inclusion p q I o') ≫
    (distinctCoordinate E I i).left ≫ q =
      (u ≫ inclusion p q I o) ≫ (distinctCoordinate E I i).left ≫ q
  simpa only [coordinate, Category.assoc] using
    congrArg (fun f ↦ u ≫ f) (labelChange_second e I o o' i)

/-- Whole original fiber completeness survives changing the distinguished label. -/
theorem labelChange_complete (hu : Complete I o u) :
    Complete I o' (u ≫ labelChange e I o o') := by
  unfold Complete
  rw [testFrame_labelChange]
  apply frameCast_complete
  exact comparisonFrame_complete e I o u hu (u ≫ coordinate p q I o o')
    (by rw [Category.assoc, coordinate_first])

/-- Completeness is intrinsic to the frame, independent of its distinguished label. -/
theorem labelChange_complete_iff :
    Complete I o' (u ≫ labelChange e I o o') ↔ Complete I o u := by
  constructor
  · intro h
    have hi := labelChange_complete e I o' o (u ≫ labelChange e I o o') h
    simpa only [Category.assoc, labelChange_comp, labelChange_self, Category.comp_id] using hi
  · exact labelChange_complete e I o o' u

end FLT.Mazur.EquivalenceRelationNormalizedFrames
