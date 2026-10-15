/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSchemePointExt

/-!
# Uniqueness and target naturality of complete polygon markings

All finite-order original markings determine the complete section uniquely.
Any map respecting those finite restrictions also respects the actual marking.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsNoetherianRing A] [IsDomain A] (hne : π ≠ 0)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every realization of the original marked stages is the original complete marking. -/
theorem completeBaseMarking_unique (i : Fin n)
    (t : Spec (.of A) ⟶ exactVeroneseProj A π n h hne hgen)
    (ht : ∀ m, baseToIntegral A π m ≫ t =
      marking A π m n h i ≫ originalStageToCompatibleProj A π hne hgen n h m) :
    t = completeBaseMarking A π hne hgen n h i := by
  apply arithmeticPoint_ext A π hgen
  intro m
  rw [ht, baseToIntegral_completeBaseMarking]

/-- The original finite marked system has exactly one realization in the complete family. -/
theorem completeBaseMarking_existsUnique (i : Fin n) :
    ∃! t : Spec (.of A) ⟶ exactVeroneseProj A π n h hne hgen,
      ∀ m, baseToIntegral A π m ≫ t =
        marking A π m n h i ≫ originalStageToCompatibleProj A π hne hgen n h m :=
  ⟨completeBaseMarking A π hne hgen n h i, baseToIntegral_completeBaseMarking A π hne hgen n h i,
    fun t ht ↦ completeBaseMarking_unique A π hgen hne n h i t ht⟩

/-- Compatibility at every original finite stage forces compatibility of actual markings. -/
@[reassoc] theorem completeBaseMarking_map_eq {Y : Scheme}
    (f : exactVeroneseProj A π n h hne hgen ⟶ Y) (i : Fin n)
    (t : Spec (.of A) ⟶ Y)
    (ht : ∀ m, marking A π m n h i ≫ originalStageToCompatibleProj A π hne hgen n h m ≫ f =
      baseToIntegral A π m ≫ t) :
    completeBaseMarking A π hne hgen n h i ≫ f = t := by
  apply arithmeticPoint_ext A π hgen
  intro m
  rw [← Category.assoc, baseToIntegral_completeBaseMarking, Category.assoc, ht]

end FLT.Mazur.PolygonArithmeticStages
