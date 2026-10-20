/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageInvariantTransitions

/-!
# The full topological coverage of rank-order transitions

Every ideal-power transition is a surjective closed immersion. The same is
true on the entire original relation by its cartesian square. No flatness of
the transition or of the rank stage over the original source is inferred.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p : D ⟶ A} [IsSeparated p] [Etale p]
local instance topologyOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance topologyOver_etale : Etale (Over.mk p).hom := ‹Etale p›
variable (n : ℕ) {k l : ℕ} (h : k ≤ l)

/-- All ideal powers retain the full underlying rank locus. -/
theorem rankStageTransition_surjective :
    Function.Surjective (rankStageTransition (Over.mk p) n h) := by
  intro y
  let I := rankStratumIdeal (Over.mk p) n
  have hy : (I ^ (l + 1)).subschemeι y ∈ Set.range (I ^ (k + 1)).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow_succ]
    have hy' := Set.mem_range_self (f := (I ^ (l + 1)).subschemeι) y
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_pow_succ] at hy'
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (I ^ (l + 1)).subschemeι.isClosedEmbedding.injective ?_⟩
  change ((rankStageTransition (Over.mk p) n h) ≫ (I ^ (l + 1)).subschemeι) x = _
  rw [rankStageTransition, Scheme.IdealSheafData.inclusion_subschemeι]
  exact hx

instance rankStageTransition_surjectiveInstance :
    Surjective (rankStageTransition (Over.mk p) n h) :=
  ⟨rankStageTransition_surjective n h⟩

/-- Every full higher-stage relation arrow lifts to the lower stage. -/
instance rankStageRelationTransition_surjective :
    Surjective (rankStageRelationTransition (p := p) n h) :=
  MorphismProperty.of_isPullback (rankStageRelationTransition_isPullback n h).flip
    (inferInstanceAs (Surjective (rankStageTransition (Over.mk p) n h)))

/-- The full arrow transition is a closed immersion, retaining all its nilpotent equations. -/
instance rankStageRelationTransition_closed :
    IsClosedImmersion (rankStageRelationTransition (p := p) n h) :=
  MorphismProperty.of_isPullback (rankStageRelationTransition_isPullback n h).flip
    (inferInstanceAs (IsClosedImmersion (rankStageTransition (Over.mk p) n h)))

end FLT.Mazur.EquivalenceRelationOrderedFrames
