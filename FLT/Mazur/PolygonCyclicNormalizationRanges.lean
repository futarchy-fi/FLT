/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicCocone
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-!
# Inverse-image ranges of cyclic normalization charts

A normalization point over node chart j lies in the left affine chart of
component j or the right affine chart of its successor. The proof retains
both possible edges in the two-gon intersection and excludes the wrong
branch using its vanishing coordinate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.PolygonCyclicNormalizationRanges
open PolygonCyclicAtlas PolygonNodeEqualizer PolygonNodeLocalization
variable (K : Type u) [Field K]

instance firstBranch_closed : IsClosedImmersion (firstBranch K) :=
  IsClosedImmersion.spec_of_surjective _ first_surjective
instance secondBranch_closed : IsClosedImmersion (secondBranch K) :=
  IsClosedImmersion.spec_of_surjective _ second_surjective

theorem first_not_right (a : ProjectiveLine.chart K) :
    firstBranch K a ∉ Set.range (PolygonNodeBranches.right K) := by
  rw [PolygonNodeBranches.range_right]
  change ¬ (y (R := K) ∉ (PrimeSpectrum.comap first.toRingHom a).asIdeal)
  change ¬¬ ((0 : Polynomial K) ∈ a.asIdeal)
  exact not_not.mpr a.asIdeal.zero_mem

theorem second_not_left (a : ProjectiveLine.chart K) :
    secondBranch K a ∉ Set.range (PolygonNodeBranches.left K) := by
  rw [PolygonNodeBranches.range_left]
  change ¬ (x (R := K) ∉ (PrimeSpectrum.comap second.toRingHom a).asIdeal)
  change ¬¬ ((0 : Polynomial K) ∈ a.asIdeal)
  exact not_not.mpr a.asIdeal.zero_mem

theorem first_eq_puncture (a : ProjectiveLine.chart K) (t : ProjectiveLine.overlap K)
    (h : PolygonNodeBranches.left K t = firstBranch K a) :
    ProjectiveLine.overlapLeft K t = a := by
  apply (firstBranch K).isClosedEmbedding.injective
  exact (congrArg (fun f ↦ f t) (overlap_firstBranch K)).trans h

theorem second_eq_puncture (a : ProjectiveLine.chart K) (t : ProjectiveLine.overlap K)
    (h : PolygonNodeBranches.right K t = secondBranch K a) :
    ProjectiveLine.overlapLeft K t = a := by
  apply (secondBranch K).isClosedEmbedding.injective
  exact (congrArg (fun f ↦ f t) (overlap_secondBranch K)).trans h

variable (n : ℕ) (hn : 2 ≤ n)

/-- The only normalization charts over node j are its two adjacent affine branches. -/
theorem component_preimage (i j : Fin n) (z : ProjectiveLine.scheme K)
    (hz : componentMap K n hn i z ∈ Set.range (chart K n hn j)) :
    (∃ a, i = j ∧ ProjectiveLine.left K a = z) ∨
      (∃ a, i = finRotate n j ∧ ProjectiveLine.right K a = z) := by
  obtain ⟨b, hb⟩ := hz
  rcases ProjectiveLine.charts_cover K z with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have he : chart K n hn i (firstBranch K a) = chart K n hn j b := by
      exact (congrArg (fun f ↦ f a) (left_componentMap K n hn i)).symm.trans hb.symm
    by_cases hij : i = j
    · exact Or.inl ⟨a, hij, rfl⟩
    rcases (charts_eq_iff K n hn hij _ _).mp he with
      ⟨t, ht, ha, _⟩ | ⟨t, _, ha, _⟩
    · have hi : i = finRotate n j := by rw [← ht, Equiv.apply_symm_apply]
      have ha' := first_eq_puncture K a t ha
      right
      refine ⟨ProjectiveLine.overlapLeft K ((ProjectiveLine.inversion K).hom t), hi, ?_⟩
      rw [← ha']
      exact (congrArg (fun f ↦ f t) (ProjectiveLine.overlap_condition K)).symm
    · exact (first_not_right K a
        ⟨(ProjectiveLine.inversion K).hom t, ha⟩).elim
  · have he : chart K n hn ((finRotate n).symm i) (secondBranch K a) =
        chart K n hn j b := by
      exact (congrArg (fun f ↦ f a) (right_componentMap K n hn i)).symm.trans hb.symm
    by_cases hij : (finRotate n).symm i = j
    · right
      exact ⟨a, by rw [← hij, Equiv.apply_symm_apply], rfl⟩
    rcases (charts_eq_iff K n hn hij _ _).mp he with
      ⟨t, _, ha, _⟩ | ⟨t, ht, ha, _⟩
    · exact (second_not_left K a ⟨t, ha⟩).elim
    · have hi : i = j := ((finRotate n).symm.injective ht).symm
      have ha' := second_eq_puncture K a ((ProjectiveLine.inversion K).hom t) ha
      left
      refine ⟨ProjectiveLine.overlapLeft K t, hi, ?_⟩
      rw [← ha']
      exact congrArg (fun f ↦ f t) (ProjectiveLine.overlap_condition K)
end FLT.Mazur.PolygonCyclicNormalizationRanges
