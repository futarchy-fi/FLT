/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteClosedFiber
public import FLT.Mazur.PolygonArithmeticFiberMarkings
public import FLT.Mazur.PolygonInfinitesimalBoundaryComparison

/-!
# Original normalization markings on the complete closed fiber

The actual reconstructed sections restrict to the original unit-one points on
the polygon, retaining the specified closed inclusion and all labels.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

local notation "K" => IsLocalRing.ResidueField A

/-- The reconstructed section restricts to its original normalization unit marking. -/
@[reassoc] theorem completeClosedBase_marking (i : Fin n) :
    completeClosedBase A ≫ completeBaseMarking A π hne hgen n h i =
      PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) 1 i ≫
        completeClosedFiberInclusion A π hne hgen n h := by
  rw [← residueBase_toIntegral A π hgen 0, Category.assoc, baseToIntegral_completeBaseMarking]
  simp only [completeClosedFiberInclusion, residueFiberInclusion, Category.assoc,
    PolygonInfinitesimal.boundarySection_zeroFiberIso_assoc,
    marking_zeroSpecialization_assoc]

/-- The closed image of the complete marking is its original normalization point. -/
theorem completeBaseMarking_closedPoint_boundary (i : Fin n) :
    completeBaseMarking A π hne hgen n h i (IsLocalRing.closedPoint A) =
      completeClosedFiberInclusion A π hne hgen n h
        (PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h)
          1 i (default : Spec (.of K))) := by
  have hb : completeClosedBase A (default : Spec (.of K)) =
      IsLocalRing.closedPoint A := IsLocalRing.PrimeSpectrum.comap_residue A _
  rw [← hb]
  exact congrArg (fun f : Spec (.of K) ⟶ exactVeroneseProj A π n h hne hgen ↦ f default)
    (completeClosedBase_marking A π hne hgen n h i)

/-- The closed-fiber isomorphism carries each original polygon marking to the actual fiber. -/
@[reassoc] theorem completeClosedFiberIso_marking (i : Fin n) :
    PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) 1 i ≫
      (completeClosedFiberIso A π hne hgen n h).hom =
        completeFiberMarking A π hne hgen n h (completeClosedBase A) i := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeClosedFiberIso_fst, completeFiberMarking_fst,
      completeClosedBase_marking]
  · rw [Category.assoc, completeClosedFiberIso_snd, completeFiberMarking_snd]
    exact PolygonMarkedSections.section_base K n _ 1 i

end FLT.Mazur.PolygonArithmeticStages
