/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicSectionOpen
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicCover

/-!
# The section image is exactly the union of the original same-label charts

The full original section covers all same-label graph charts. Any remaining
point of the literal adic graph must lie in a chart with unequal node labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "t" => parameter K (m + 1)
local notation "f" => completeIdentityAdicGraphSection K n h (m + 1)

/-- Every full same-label chart factors through the actual original whole-input section. -/
@[reassoc] theorem completeIdentityAdicDiagonalChart_section (i : Fin n) :
    completeIdentityActionGraphAdicChartInclusion K n h (m + 1) i i =
      completeIdentityActionGraphAdicChartSource K n h (m + 1) i i ≫
        chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i ≫ (f) := by
  rw [← completeIdentityAdicNodeSection_inclusion, ← Category.assoc,
    completeIdentityAdicNodeSection_inverse, Category.id_comp]

/-- Membership in the section open is exactly membership in some original same-label chart. -/
theorem completeIdentityAdicSectionOpen_mem_iff
    (x : completeIdentityActionGraphStage K n h (m + 1)) :
    x ∈ completeIdentityAdicSectionOpen K n h m ↔
      ∃ i, x ∈ Set.range (completeIdentityActionGraphAdicChartInclusion K n h (m + 1) i i) := by
  change x ∈ (completeIdentityAdicSectionOpen K n h m : Set _) ↔ _
  rw [completeIdentityAdicSectionOpen_carrier]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨i, z, hz⟩ := charts_cover (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h y
    refine ⟨i, completeIdentityAdicNodeSection K n h (m + 1) i z, ?_⟩
    change (completeIdentityAdicNodeSection K n h (m + 1) i ≫
      completeIdentityActionGraphAdicChartInclusion K n h (m + 1) i i) z = (f) y
    rw [completeIdentityAdicNodeSection_inclusion]
    change (f) (chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i z) = (f) y
    rw [hz]
  · rintro ⟨i, y, rfl⟩
    rw [completeIdentityAdicDiagonalChart_section]
    exact ⟨_, rfl⟩

/-- Any remaining graph point requires genuinely different original source and target labels. -/
theorem completeIdentityAdicSectionOpen_complement_chart
    (x : completeIdentityActionGraphStage K n h (m + 1))
    (hx : x ∉ completeIdentityAdicSectionOpen K n h m) :
    ∃ i j, i ≠ j ∧
      x ∈ Set.range (completeIdentityActionGraphAdicChartInclusion K n h (m + 1) i j) := by
  obtain ⟨i, j, hij⟩ := completeIdentityActionGraphAdicChart_covers K n h (m + 1) x
  refine ⟨i, j, ?_, hij⟩
  intro he
  subst j
  exact hx ((completeIdentityAdicSectionOpen_mem_iff K n h m x).mpr ⟨i, hij⟩)

end FLT.Mazur.PolygonInfinitesimalStages
