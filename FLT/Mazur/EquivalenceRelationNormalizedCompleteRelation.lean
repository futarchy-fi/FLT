/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedActionRelation
public import FLT.Mazur.RelativeFrameCompletenessTransfer

/-!
# One complete endpoint suffices for the full normalized relation

Whole-fiber rebasing and finite cardinality force a related distinct frame of
the same size to be complete. Thus the comparison with the permutation relation
contains every full original arrow with a complete first endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

local instance completeRelationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance completeRelationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local notation "E" => Over.mk p
variable {K : Type} [Field K] (u v : Spec (.of K) ⟶ source p q I o)
  (a : Spec (.of K) ⟶ D)
  (ha : a ≫ p = u ≫ first p q I o) (hb : a ≫ q = v ≫ first p q I o)

include e a ha hb in
/-- Completeness passes along every full original arrow between equal-size frames. -/
theorem complete_of_original_arrow (hu : Complete I o u) : Complete I o v := by
  have ht := comparisonFrame_complete e I o u hu a ha
  have hv := complete_of_complete_frame E I (comparisonFrame e I o u a ha)
    (targetFrame I o v a hb) ht
  have hc := frameCast_complete I hb (targetFrame I o v a hb) hv
  have he : frameCast I hb (targetFrame I o v a hb) = testFrame I o v := by
    apply Over.OverMorphism.ext
    rfl
  rwa [he] at hc

include e in
/-- A complete first endpoint forces completeness of the independent second endpoint. -/
theorem relation_complete_second
    (z : Spec (.of K) ⟶ fullRelation p q I o)
    (hz : Complete I o (z ≫ relationFirst p q I o)) :
    Complete I o (z ≫ relationSecond p q I o) := by
  apply complete_of_original_arrow e I o (z ≫ relationFirst p q I o)
    (z ≫ relationSecond p q I o) (z ≫ relationArrow p q I o) _ _ hz
  · simp only [Category.assoc, relationArrow_first]
  · simp only [Category.assoc, relationArrow_second]

/-- No original geometric arrow from a complete frame is discarded by the comparison. -/
theorem complete_first_factors_relationComparison
    (z : Spec (.of K) ⟶ fullRelation p q I o)
    (hz : Complete I o (z ≫ relationFirst p q I o)) :
    ∃ w : Spec (.of K) ⟶ permutationRelation (p := p) (q := q) I o,
      w ≫ relationComparison e I o = z :=
  complete_factors_relationComparison e I o z hz (relation_complete_second e I o z hz)

include a ha hb in
/-- A single completeness hypothesis recovers the unique permutation of related frames. -/
theorem complete_original_arrow_unique_permutation (hu : Complete I o u) :
    ∃! σ : Equiv.Perm I, u ≫ (action e I o σ).hom = v := by
  have hv := complete_of_original_arrow e I o u v a ha hb hu
  exact (original_arrow_iff_unique_permutation e I o u v hu hv).mp ⟨a, ha, hb⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
