/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameComparison
public import FLT.Mazur.RelativeFrameRelabelCompleteness

/-!
# Completeness under the endpoint-moving normalized action

The moved test frame is the relabeling of its whole-fiber transport along the
actual original action arrow. Thus every point of a complete geometric orbit
remains complete, although completeness need not hold on an open neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

local instance completeActionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local notation "E" => Over.mk p
variable {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)
  (σ : Equiv.Perm I)

/-- The moved test frame is the relabeled whole original fiber transport. -/
theorem testFrame_action :
    testFrame I o (u ≫ (action e I o σ).hom) =
      frameCast I (by rw [Category.assoc, actionArrow_second e, Category.assoc])
        (frameRelabel E I
          (comparisonFrame e I o u (u ≫ actionArrow I o σ)
            (by rw [Category.assoc, actionArrow_first])) σ) := by
  apply frame_ext_second e I
  intro i
  change (testFrame I o (u ≫ (action e I o σ).hom) ≫
    distinctCoordinate E I i).left ≫ q =
      (frameRelabel E I (comparisonFrame e I o u (u ≫ actionArrow I o σ)
        (by rw [Category.assoc, actionArrow_first])) σ ≫
          distinctCoordinate E I i).left ≫ q
  rw [frameRelabel_coordinate]
  have hr := rebaseFrame_second e I (u ≫ actionArrow (p := p) (q := q) I o σ)
    (frameCast I (by rw [Category.assoc, actionArrow_first]) (testFrame I o u)) (σ.symm i)
  change _ = (rebaseFrame e I (u ≫ actionArrow I o σ) _ ≫
    distinctCoordinate E I (σ.symm i)).left ≫ q
  rw [hr]
  change ((u ≫ actionMap e I o σ) ≫ inclusion p q I o) ≫
    (distinctCoordinate E I i).left ≫ q =
      (u ≫ inclusion p q I o) ≫ (distinctCoordinate E I (σ.symm i)).left ≫ q
  simpa only [coordinate, Category.assoc] using
    congrArg (fun f ↦ u ≫ f) (actionMap_second e I o σ i)

/-- The normalized action preserves completeness of the entire original fiber. -/
theorem action_complete (hu : Complete I o u) :
    Complete I o (u ≫ (action e I o σ).hom) := by
  unfold Complete
  rw [testFrame_action]
  apply frameCast_complete
  apply frameRelabel_complete
  exact comparisonFrame_complete e I o u hu (u ≫ actionArrow I o σ)
    (by rw [Category.assoc, actionArrow_first])

/-- Completeness is invariant in both directions under each normalized permutation. -/
theorem action_complete_iff :
    Complete I o (u ≫ (action e I o σ).hom) ↔ Complete I o u := by
  constructor
  · intro h
    have hi := action_complete e I o (u ≫ (action e I o σ).hom) σ⁻¹ h
    have he : (u ≫ (action e I o σ).hom) ≫ (action e I o σ⁻¹).hom = u := by
      change (u ≫ actionMap e I o σ) ≫ actionMap e I o σ⁻¹ = u
      rw [Category.assoc, ← actionMap_mul, inv_mul_cancel, actionMap_one, Category.comp_id]
    rwa [he] at hi
  · exact action_complete e I o u σ

end FLT.Mazur.EquivalenceRelationNormalizedFrames
