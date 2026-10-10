/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesEquation

/-!
# Two standard opens cover the entire successive Rees scheme

The vertical generator is in every prime containing the other two. The
scale and horizontal standard opens therefore cover the full Rees Proj,
including all of its vertical-generator chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

/-- The actual center retains all three preceding generators. -/
def centerGenerators : Fin 3 → B := ![algebraMap R B π, BX, BY]

/-- Each of the three generators belongs to the preceding modification center. -/
theorem centerGenerators_mem (i : Fin 3) : centerGenerators W s π b3 b4 b6 i ∈ I := by
  fin_cases i <;> exact Ideal.subset_span (by simp [centerGenerators])

/-- The chosen generators span precisely the preceding modification center. -/
theorem centerGenerators_span :
    Ideal.span (Set.range (centerGenerators W s π b3 b4 b6)) = I := by
  simp only [centerGenerators, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, WeierstrassSuccessiveX.modificationCenter]

/-- Every point lies in the scale or horizontal open; the vertical chart adds no complement. -/
theorem mem_scale_or_horizontal (z : BlowupRees.proj I) :
    z ∈ BlowupRees.generatorOpen I (algebraMap R B π) (Ideal.subset_span (by simp)) ∨
      z ∈ BlowupRees.generatorOpen I BX (Ideal.subset_span (by simp)) := by
  change scaleGenerator W s π b3 b4 b6 ∉ z.asHomogeneousIdeal ∨
    horizontalGenerator W s π b3 b4 b6 ∉ z.asHomogeneousIdeal
  by_contra hz
  push Not at hz
  have hy := verticalGenerator_mem_of_scale_horizontal W s π b3 b4 b6
    z.asHomogeneousIdeal.toIdeal hz.1 hz.2
  apply z.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant (BlowupRees.component I)).toIdeal ≤
    z.asHomogeneousIdeal.toIdeal
  rw [BlowupRees.irrelevant_eq_span_of_span I (centerGenerators W s π b3 b4 b6)
    (centerGenerators_mem W s π b3 b4 b6) (centerGenerators_span W s π b3 b4 b6)]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hz.1
  · exact hz.2
  · exact hy

/-- The scale and horizontal generator opens have union the entire Rees scheme. -/
theorem generatorOpen_sup_eq_top :
    BlowupRees.generatorOpen I (algebraMap R B π) (Ideal.subset_span (by simp)) ⊔
      BlowupRees.generatorOpen I BX (Ideal.subset_span (by simp)) = ⊤ := by
  apply top_unique
  intro z _
  exact mem_scale_or_horizontal W s π b3 b4 b6 z

/-- Every Rees point is in one of the two actual fraction charts. -/
theorem fraction_charts_cover (z : BlowupRees.proj I) :
    (∃ a, BlowupRees.fractionChartInclusion I (algebraMap R B π)
      (Ideal.subset_span (by simp)) a = z) ∨
    ∃ a, BlowupRees.fractionChartInclusion I BX (Ideal.subset_span (by simp)) a = z := by
  have h := mem_scale_or_horizontal W s π b3 b4 b6 z
  rcases h with h | h
  · left
    rw [← BlowupRees.fractionChartInclusion_range] at h
    exact h
  · right
    rw [← BlowupRees.fractionChartInclusion_range] at h
    exact h

end FLT.Mazur.WeierstrassSuccessiveRees
