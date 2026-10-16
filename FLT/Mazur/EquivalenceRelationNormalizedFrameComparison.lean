/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameFree
public import FLT.Mazur.EquivalenceRelationFrameRebaseGeometric

/-!
# Comparing normalized complete frames along the full original relation

On complete geometric frames every original relation arrow is realized by exactly
one normalized permutation. Conversely each permutation supplies an original arrow.
This is a geometric comparison; an open cover on which completeness holds and a
scheme-level identification of the two relations still require separate proofs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

local instance compareOverFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance compareOverFirst_etale : Etale (Over.mk p).hom := ‹Etale p›
local notation "E" => Over.mk p
local notation "N" => source p q I o
variable {K : Type} [Field K] (u v : Spec (.of K) ⟶ source p q I o)

/-- The entire original frame on a test of the normalized source. -/
def testFrame : Over.mk (u ≫ first p q I o) ⟶ distinctScheme E I :=
  framePull I (frame p q I o) u

/-- Completeness refers to the whole original first-endpoint fiber. -/
def Complete : Prop :=
  Function.Bijective (fun i ↦ geometricCoordinate E I (testFrame I o u) i default)

variable (hu : Complete I o u) (hv : Complete I o v)
  (a : Spec (.of K) ⟶ D)
  (ha : a ≫ p = u ≫ first p q I o) (hb : a ≫ q = v ≫ first p q I o)

/-- Transport the original complete frame to the other actual first endpoint. -/
def comparisonFrame : Over.mk (a ≫ q) ⟶ distinctScheme E I :=
  rebaseFrame e I a (frameCast I ha.symm (testFrame I o u))

include hu in
omit [Etale p] in
/-- Transport retains completeness of the entire original geometric fiber. -/
theorem comparisonFrame_complete :
    Function.Bijective (fun i ↦ geometricCoordinate E I
      (comparisonFrame e I o u a ha) i default) := by
  exact rebaseFrame_complete e I a _ (frameCast_complete I ha.symm _ hu)

/-- The other normalized frame over the displayed target endpoint. -/
def targetFrame : Over.mk (a ≫ q) ⟶ distinctScheme E I :=
  frameCast I hb.symm (testFrame I o v)

include hv in
omit [Etale p] in
/-- Displaying the same target endpoint differently does not change completeness. -/
theorem targetFrame_complete :
    Function.Bijective (fun i ↦ geometricCoordinate E I (targetFrame I o v a hb) i default) := by
  exact frameCast_complete I hb.symm _ hv

/-- The permutation comparing the complete frames after the full original transport. -/
def comparisonPermutation : Equiv.Perm I :=
  completeFrameRelabel E I (comparisonFrame e I o u a ha)
    (comparisonFrame_complete e I o u hu a ha) (targetFrame I o v a hb)
    (targetFrame_complete I o v hv a hb)

/-- Every original arrow between complete normalized frames is realized by the action. -/
theorem comparisonPermutation_action :
    u ≫ (action e I o (comparisonPermutation e I o u v hu hv a ha hb)).hom = v := by
  apply hom_ext_second p q I o e
  intro i
  change (u ≫ actionMap e I o _) ≫ coordinate p q I o i ≫ q = _
  rw [Category.assoc, actionMap_second]
  have hc := congrArg (fun z : Over.mk (a ≫ q) ⟶ E ↦ z.left ≫ q)
    (completeFrameRelabel_coordinate E I (comparisonFrame e I o u a ha)
      (comparisonFrame_complete e I o u hu a ha) (targetFrame I o v a hb)
      (targetFrame_complete I o v hv a hb) i)
  have hr := rebaseFrame_second e I a (frameCast I ha.symm (testFrame I o u))
    ((comparisonPermutation e I o u v hu hv a ha hb).symm i)
  change (rebaseFrame e I a (frameCast I ha.symm (testFrame I o u)) ≫
    distinctCoordinate E I ((comparisonPermutation e I o u v hu hv a ha hb).symm i)).left ≫ q =
      (targetFrame I o v a hb ≫ distinctCoordinate E I i).left ≫ q at hc
  rw [hr] at hc
  simpa only [targetFrame, testFrame, frameCast, framePull, frame,
    Over.homMk_left, Over.comp_left, coordinate, Category.assoc] using hc

include hu hv in
/-- The full original geometric relation is equivalent to a unique normalized permutation. -/
theorem original_arrow_iff_unique_permutation :
    (∃ a : Spec (.of K) ⟶ D,
      a ≫ p = u ≫ first p q I o ∧ a ≫ q = v ≫ first p q I o) ↔
      ∃! σ : Equiv.Perm I, u ≫ (action e I o σ).hom = v := by
  constructor
  · rintro ⟨a, ha, hb⟩
    refine ⟨comparisonPermutation e I o u v hu hv a ha hb,
      comparisonPermutation_action e I o u v hu hv a ha hb, ?_⟩
    intro σ hσ
    exact action_unique e I o u v σ _ hσ
      (comparisonPermutation_action e I o u v hu hv a ha hb)
  · rintro ⟨σ, hσ, _⟩
    refine ⟨u ≫ actionArrow (p := p) (q := q) I o σ, ?_, ?_⟩
    · rw [Category.assoc, actionArrow_first]
    · rw [Category.assoc, actionArrow_second e, ← Category.assoc, hσ]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
