/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesSchemePointExt

/-!
# Uniqueness and target naturality of complete polygon markings

All finite-order original markings determine the complete section uniquely.
Any map respecting those finite restrictions also respects the actual marking.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every realization of the original marked stages is the original complete marking. -/
theorem completeBaseMarking_unique (i : Fin n)
    (t : Spec (.of (PowerSeries K)) ⟶ exactVeroneseProj K n h)
    (ht : ∀ m, baseToSeries K m ≫ t =
      marking K m n h i ≫ originalStageToCompatibleProj K n h m) :
    t = completeBaseMarking K n h i := by
  apply powerSeriesPoint_ext K
  intro m
  rw [ht, baseToSeries_completeBaseMarking]

/-- The original finite marked system has exactly one realization in the complete family. -/
theorem completeBaseMarking_existsUnique (i : Fin n) :
    ∃! t : Spec (.of (PowerSeries K)) ⟶ exactVeroneseProj K n h,
      ∀ m, baseToSeries K m ≫ t =
        marking K m n h i ≫ originalStageToCompatibleProj K n h m :=
  ⟨completeBaseMarking K n h i, baseToSeries_completeBaseMarking K n h i,
    fun t ht ↦ completeBaseMarking_unique K n h i t ht⟩

/-- Compatibility at every original finite stage forces compatibility of actual markings. -/
@[reassoc] theorem completeBaseMarking_map_eq {Y : Scheme}
    (f : exactVeroneseProj K n h ⟶ Y) (i : Fin n)
    (t : Spec (.of (PowerSeries K)) ⟶ Y)
    (ht : ∀ m, marking K m n h i ≫ originalStageToCompatibleProj K n h m ≫ f =
      baseToSeries K m ≫ t) :
    completeBaseMarking K n h i ≫ f = t := by
  apply powerSeriesPoint_ext K
  intro m
  rw [← Category.assoc, baseToSeries_completeBaseMarking, Category.assoc, ht]

end FLT.Mazur.PolygonInfinitesimalStages
