/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarFullAtlas

/-!
# Exact coverage comparison for a scalar chart

The scalar pullback of a chart maps to the entire original scalar pullback
by an actual cartesian square. Its image is exactly the inverse image of
the original chart image. Equal scalar values alone give no coverage claim.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarRelationPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {U X S Y : Scheme.{0}} (j : U ⟶ X) (s : X ⟶ S) (b : Y ⟶ S)

/-- The canonical comparison from a chart test to the whole original source test. -/
def sourceComparison : testSource (j ≫ s) b ⟶ testSource s b :=
  (IsPullback.of_hasPullback s b).flip.lift (pullback.snd (j ≫ s) b)
    (pullback.fst (j ≫ s) b ≫ j)
    (by rw [Category.assoc, pullback.condition])

@[simp, reassoc]
theorem sourceComparison_fst : sourceComparison j s b ≫ pullback.fst s b =
    pullback.fst (j ≫ s) b ≫ j :=
  (IsPullback.of_hasPullback s b).flip.lift_snd _ _ _

@[simp, reassoc]
theorem sourceComparison_snd : sourceComparison j s b ≫ pullback.snd s b =
    pullback.snd (j ≫ s) b :=
  (IsPullback.of_hasPullback s b).flip.lift_fst _ _ _

/-- The source comparison is actual base change of the original chart map. -/
theorem sourceComparison_isPullback : IsPullback (sourceComparison j s b)
    (pullback.fst (j ≫ s) b) (pullback.fst s b) j :=
  (IsPullback.of_hasPullback (j ≫ s) b).flip.of_right'
    (IsPullback.of_hasPullback s b).flip

/-- Original etaleness survives this comparison, without a surjectivity assumption. -/
instance sourceComparisonEtale [Etale j] : Etale (sourceComparison j s b) :=
  MorphismProperty.of_isPullback (sourceComparison_isPullback j s b).flip inferInstance

/-- The comparison image is controlled by the full original chart image. -/
theorem sourceComparison_range : Set.range (sourceComparison j s b) =
    pullback.fst s b ⁻¹' Set.range j := by
  simpa only [Set.preimage_univ, Set.image_univ] using
    Scheme.image_preimage_eq_of_isPullback (sourceComparison_isPullback j s b).flip Set.univ

/-- Covering every original scalar-test point is precisely the remaining image condition. -/
theorem sourceComparison_surjective_iff : Function.Surjective (sourceComparison j s b) ↔
    ∀ x : testSource s b, pullback.fst s b x ∈ Set.range j := by
  rw [← Set.range_eq_univ, sourceComparison_range, Set.eq_univ_iff_forall]
  rfl

/-- The image condition makes the actual chart comparison an fppf cover. -/
theorem sourceComparison_covers [Etale j]
    (h : ∀ x : testSource s b, pullback.fst s b x ∈ Set.range j) :
    Presieve.singleton (sourceComparison j s b) ∈
      Scheme.fppfPrecoverage (testSource s b) := by
  let _ : Surjective (sourceComparison j s b) :=
    ⟨(sourceComparison_surjective_iff j s b).mpr h⟩
  exact Scheme.Hom.singleton_mem_fppfPrecoverage _

end FLT.Mazur.SchemeScalarRelationPullback
