/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageConstants
public import FLT.Mazur.PolygonArithmeticTowerDivision

/-!
# Scalar division in the retained degree-zero tower

The proved structural coefficient comparison supplies adjacent lifting in
degree zero. The original scalar exactness then gives compatible power
division in that degree, with no positivity assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

include hne hgen in
/-- Actual adjacent homogeneous transitions lift all degree-zero sections. -/
theorem boundaryIntegralDegree_zero_surjective (m : ℕ) :
    Function.Surjective (boundaryIntegralDegreeTransition A π n h m 0) := by
  apply boundaryDegreeTransition_surjective A π n h m 0
  intro s
  obtain ⟨r, hr⟩ := stageScalars_surjective A π n h hgen hne m s
  obtain ⟨t, ht⟩ := restriction_surjective A π m r
  refine ⟨stageScalars A π (m + 1) n h t, ?_⟩
  exact (SectionGradedLinePullback.sectionMap_zero _ _ ⊤ _).trans
    ((stageRestriction_stageScalars A π n h m t).trans
      ((congrArg (stageScalars A π m n h) ht).trans hr))

include hne hgen in
/-- The original degree-zero linear transition has precisely its last scalar-power kernel. -/
theorem boundaryIntegralDegree_zero_kernel (m : ℕ)
    (s : boundaryIntegralDegree A π n h (m + 1) 0) :
    boundaryIntegralDegreeTransition A π n h m 0 s = 0 ↔
      ∃ t, π ^ (m + 1) • t = s := by
  obtain ⟨s, ⟨u, rfl⟩⟩ := s
  rw [Subtype.ext_iff]
  change boundarySectionsMap A π n h (homOfLE (Nat.le_succ m))
    (of (boundaryLine A π (m + 1) n h) ⊤ 0 u) = 0 ↔ _
  rw [boundarySectionsMap_adjacent_ringHom, SectionGradedLinePullback.ringHom_of_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (boundarySections_zero_scalar_exact A π hgen n h hne m u).mp hz
    refine ⟨⟨of (boundaryLine A π (m + 1) n h) ⊤ 0 v, ⟨v, rfl⟩⟩, Subtype.ext ?_⟩
    rw [boundaryIntegralDegree_parameterPower_val, boundaryIntegralScalars_power_of]
    exact congrArg (of (boundaryLine A π (m + 1) n h) ⊤ 0) hv
  · rintro ⟨⟨t, ⟨v, rfl⟩⟩, ht⟩
    have he := congrArg Subtype.val ht
    rw [boundaryIntegralDegree_parameterPower_val, boundaryIntegralScalars_power_of] at he
    exact (boundarySections_zero_scalar_exact A π hgen n h hne m u).mpr
      ⟨v, DirectSum.of_injective 0 he⟩

include hne hgen in
/-- Every original degree-zero evaluation kernel admits an adjacent-compatible power division. -/
theorem boundaryIntegralDegree_zero_powerDivision (m : ℕ)
    (s : ∀ a, boundaryIntegralDegree A π n h a 0)
    (hs : ScalarTowerDivision.Compatible
      (fun a ↦ boundaryIntegralDegreeTransition A π n h a 0) s) (hz : s m = 0) :
    ∃ t : ∀ a, boundaryIntegralDegree A π n h a 0,
      ScalarTowerDivision.Compatible (fun a ↦ boundaryIntegralDegreeTransition A π n h a 0) t ∧
      ∀ a, π ^ (m + 1) • t a = s a :=
  ScalarTowerDivision.exists_compatible_power_division π
    (fun a ↦ boundaryIntegralDegreeTransition A π n h a 0)
    (boundaryIntegralDegree_zero_surjective A π hne hgen n h)
    (boundaryIntegralDegree_zero_kernel A π hne hgen n h)
    (fun a ↦ boundaryIntegralDegree_annihilator A π hne n h a 0) m s hs hz

end FLT.Mazur.PolygonArithmeticStages
