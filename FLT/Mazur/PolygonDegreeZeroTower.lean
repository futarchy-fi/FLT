/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageScalarComparison
public import FLT.Mazur.PolygonSeriesTowerDivision

/-!
# Scalar division in the retained degree-zero tower

The proved structural coefficient comparison supplies adjacent lifting in
degree zero. The original scalar exactness then gives compatible power
division in that degree, with no positivity assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Actual adjacent homogeneous transitions lift all degree-zero sections. -/
theorem boundarySeriesDegree_zero_surjective (m : ℕ) :
    Function.Surjective (boundarySeriesDegreeTransition K n h m 0) := by
  apply boundaryDegreeTransition_surjective K n h m 0
  intro s
  obtain ⟨r, hr⟩ := stageScalars_surjective K n h m s
  obtain ⟨t, ht⟩ := restriction_surjective K m r
  refine ⟨stageScalars K (m + 1) n h t, ?_⟩
  exact (SectionGradedLinePullback.sectionMap_zero _ _ ⊤ _).trans
    ((stageRestriction_stageScalars K n h m t).trans
      ((congrArg (stageScalars K m n h) ht).trans hr))

/-- The original degree-zero linear transition has precisely its last scalar-power kernel. -/
theorem boundarySeriesDegree_zero_kernel (m : ℕ)
    (s : boundarySeriesDegree K n h (m + 1) 0) :
    boundarySeriesDegreeTransition K n h m 0 s = 0 ↔
      ∃ t, (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s := by
  obtain ⟨s, ⟨u, rfl⟩⟩ := s
  rw [Subtype.ext_iff]
  change boundarySectionsMap K n h (homOfLE (Nat.le_succ m))
    (of (boundaryLine K (m + 1) n h) ⊤ 0 u) = 0 ↔ _
  rw [boundarySectionsMap_adjacent_ringHom, SectionGradedLinePullback.ringHom_of_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (boundarySections_zero_scalar_exact K n h m u).mp hz
    refine ⟨⟨of (boundaryLine K (m + 1) n h) ⊤ 0 v, ⟨v, rfl⟩⟩, Subtype.ext ?_⟩
    rw [boundarySeriesDegree_parameterPower_val, boundarySeriesScalars_power_of]
    exact congrArg (of (boundaryLine K (m + 1) n h) ⊤ 0) hv
  · rintro ⟨⟨t, ⟨v, rfl⟩⟩, ht⟩
    have he := congrArg Subtype.val ht
    rw [boundarySeriesDegree_parameterPower_val, boundarySeriesScalars_power_of] at he
    exact (boundarySections_zero_scalar_exact K n h m u).mpr
      ⟨v, DirectSum.of_injective 0 he⟩

/-- Every original degree-zero evaluation kernel admits an adjacent-compatible power division. -/
theorem boundarySeriesDegree_zero_powerDivision (m : ℕ)
    (s : ∀ a, boundarySeriesDegree K n h a 0)
    (hs : ScalarTowerDivision.Compatible
      (fun a ↦ boundarySeriesDegreeTransition K n h a 0) s) (hz : s m = 0) :
    ∃ t : ∀ a, boundarySeriesDegree K n h a 0,
      ScalarTowerDivision.Compatible (fun a ↦ boundarySeriesDegreeTransition K n h a 0) t ∧
      ∀ a, (PowerSeries.X : PowerSeries K) ^ (m + 1) • t a = s a :=
  ScalarTowerDivision.exists_compatible_power_division PowerSeries.X
    (fun a ↦ boundarySeriesDegreeTransition K n h a 0)
    (boundarySeriesDegree_zero_surjective K n h) (boundarySeriesDegree_zero_kernel K n h)
    (fun a ↦ boundarySeriesDegree_annihilator K n h a 0) m s hs hz

end FLT.Mazur.PolygonInfinitesimalStages
