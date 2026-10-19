/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameStrictExtension
public import FLT.Mazur.EquivalenceRelationNormalizedFrameComparison

/-!
# Extend an incomplete normalized original frame

The extra section gives a larger normalized frame over the same field and
first endpoint. Every old arrow is retained, including the distinguished
identity coordinate. The new arrow is distinct from all of them.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I) {K : Type} [Field K]
  (u : Spec (.of K) ⟶ source p q I o)
local instance strictExtensionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance strictExtensionOver_etale : Etale (Over.mk p).hom := ‹Etale p›

omit [Etale p] in
/-- Evaluating a test-frame coordinate retains the actual normalized original arrow. -/
theorem testFrame_original_coordinate (i : I) :
    (testFrame I o u ≫ distinctCoordinate (Over.mk p) I i).left =
      u ≫ coordinate p q I o i := Category.assoc _ _ _

variable [IsSepClosed K]

/-- An incomplete original frame has a strictly larger normalized extension at the same endpoint. -/
theorem exists_strict_normalized_extension (hu : ¬ Complete I o u) :
    ∃ v : Spec (.of K) ⟶ source p q (Option I) (some o),
      v ≫ first p q (Option I) (some o) = u ≫ first p q I o ∧
      (∀ i, v ≫ coordinate p q (Option I) (some o) (some i) =
        u ≫ coordinate p q I o i) ∧
      ∀ i, v ≫ coordinate p q (Option I) (some o) none ≠
        u ≫ coordinate p q I o i := by
  obtain ⟨t, ht, hn⟩ := exists_strict_original_extension (Over.mk p) I (testFrame I o u) hu
  have h : u ≫ first p q I o =
      (t ≫ distinctCoordinate (Over.mk p) (Option I) (some o)).left ≫ q := by
    rw [ht, testFrame_original_coordinate, Category.assoc, ← first_eq_distinguished]
  refine ⟨lift p q (Option I) (some o) t h, lift_first p q (Option I) (some o) t h,
    fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rw [lift_coordinate, ht, testFrame_original_coordinate]
  · apply hn i
    apply Over.OverMorphism.ext
    rw [testFrame_original_coordinate, ← lift_coordinate p q (Option I) (some o) t h]
    exact hi

end FLT.Mazur.EquivalenceRelationNormalizedFrames
