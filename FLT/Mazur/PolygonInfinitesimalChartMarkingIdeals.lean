/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalCartier
public import FLT.Mazur.PolygonSmoothingMarkingIdealSheaf
public import FLT.Mazur.ProjectiveLineMarkedCharts

/-!
# The original global marking ideal on each arithmetic node chart

The same marking has its outgoing equation on its own chart and its incoming
equation on the preceding chart. All other charts see the unit ideal. These
are equalities of full ideal sheaves, including both edges of the two-gon.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n) (i : Fin n) (a : Rˣ)

/-- The actual incoming section glues to the same global marked section. -/
@[reassoc] theorem incomingMarkedSection_chart :
    incomingMarkedSection t a ≫ chart R t n h ((finRotate n).symm i) =
      marking R t n h i a := by
  rw [← markedTorusSection_preceding, Category.assoc, ← overlap,
    ← Category.assoc, markedTorusSection_left, marking]

/-- On its original chart the global section ideal is the outgoing section kernel. -/
theorem marking_ideal_own_chart :
    (marking R t n h i a).ker.comap (chart R t n h i) =
      (markedSection t a).ker := by
  let _ := PolygonInfinitesimalSeparated.separated R t n h
  let _ := FCurve.isClosedImmersion_section _ _ (marking_base R t n h i a)
  have : IsClosedImmersion (markedSection t a ≫ chart R t n h i) :=
    inferInstanceAs (IsClosedImmersion (marking R t n h i a))
  exact ProjectiveLineMarkedCharts.ker_comap_mono (markedSection t a) (chart R t n h i)

/-- On the preceding chart it is the kernel of the original inverse-Laurent marking. -/
theorem marking_ideal_preceding_chart :
    (marking R t n h i a).ker.comap (chart R t n h ((finRotate n).symm i)) =
      (incomingMarkedSection t a).ker := by
  let _ := PolygonInfinitesimalSeparated.separated R t n h
  let _ := FCurve.isClosedImmersion_section _ _ (marking_base R t n h i a)
  have : IsClosedImmersion
      (incomingMarkedSection t a ≫ chart R t n h ((finRotate n).symm i)) := by
    rw [incomingMarkedSection_chart]
    infer_instance
  rw [← incomingMarkedSection_chart R t n h i a,
    ProjectiveLineMarkedCharts.ker_comap_mono]

/-- No other arithmetic node chart contains a point of this marking. -/
theorem marking_not_mem_other_chart {j : Fin n} (hji : j ≠ i)
    (hprev : j ≠ (finRotate n).symm i) (x : PolygonSmoothing.chart R t) :
    chart R t n h j x ∉ Set.range (marking R t n h i a) := by
  rintro ⟨z, hz⟩
  have he : chart R t n h j x = chart R t n h i (markedSection t a z) := hz.symm
  rcases (charts_eq_iff R t n h hji _ _).mp he with
    ⟨w, _, _, hw⟩ | ⟨_, hij, _, _⟩
  · exact markedSection_not_mem_preceding R t a z ⟨w, hw⟩
  · exact hprev hij.symm

/-- The global marking ideal is exactly the unit ideal on every other full chart. -/
theorem marking_ideal_other_chart {j : Fin n} (hji : j ≠ i)
    (hprev : j ≠ (finRotate n).symm i) :
    (marking R t n h i a).ker.comap (chart R t n h j) = ⊤ := by
  let _ := PolygonInfinitesimalSeparated.separated R t n h
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change chart R t n h j x ∈ (marking R t n h i a).ker.support ↔ False
  rw [← SetLike.mem_coe,
    FCurve.support_section_ker _ _ (marking_base R t n h i a)]
  exact iff_false_intro (marking_not_mem_other_chart R t n h i a hji hprev x)

end FLT.Mazur.PolygonInfinitesimal
