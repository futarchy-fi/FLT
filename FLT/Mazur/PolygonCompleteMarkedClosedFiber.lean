/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedFiber
public import FLT.Mazur.PolygonCompleteFiberMarkings
public import FLT.Mazur.PolygonInfinitesimalBoundaryComparison

/-!
# Original normalization markings on the complete closed fiber

The actual reconstructed sections restrict to the original unit-one points on
the polygon, retaining the specified closed inclusion and all labels.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The reconstructed section restricts to its original normalization unit marking. -/
@[reassoc] theorem completeClosedBase_marking (i : Fin n) :
    completeClosedBase K ≫ completeBaseMarking K n h i =
      PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) 1 i ≫
        completeClosedFiberInclusion K n h := by
  rw [← reductionBase_toSeries K 0, Category.assoc, baseToSeries_completeBaseMarking]
  simp only [completeClosedFiberInclusion, specialFiberInclusion, Category.assoc,
    PolygonInfinitesimal.boundarySection_zeroFiberIso_assoc,
    marking_zeroSpecialization_assoc]

/-- The closed image of the complete marking is its original normalization point. -/
theorem completeBaseMarking_closedPoint_boundary (i : Fin n) :
    completeBaseMarking K n h i (IsLocalRing.closedPoint (PowerSeries K)) =
      completeClosedFiberInclusion K n h
        (PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h)
          1 i (default : Spec (.of K))) := by
  have hb : completeClosedBase K (default : Spec (.of K)) =
      IsLocalRing.closedPoint (PowerSeries K) := by
    rw [← reductionBase_toSeries K 0]
    exact baseToSeries_stageBasePoint K 0
  rw [← hb]
  exact congrArg (fun f : Spec (.of K) ⟶ exactVeroneseProj K n h ↦ f default)
    (completeClosedBase_marking K n h i)

/-- The closed-fiber isomorphism carries each original polygon marking to the actual fiber. -/
@[reassoc] theorem completeClosedFiberIso_marking (i : Fin n) :
    PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) 1 i ≫
      (completeClosedFiberIso K n h).hom = completeFiberMarking K n h (completeClosedBase K) i := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeClosedFiberIso_fst, completeFiberMarking_fst,
      completeClosedBase_marking]
  · rw [Category.assoc, completeClosedFiberIso_snd, completeFiberMarking_snd]
    exact PolygonMarkedSections.section_base K n _ 1 i

end FLT.Mazur.PolygonInfinitesimalStages
