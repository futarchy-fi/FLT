/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundarySeriesDegree
public import FLT.Mazur.PolygonBoundaryGradedExactness
public import FLT.Mazur.ScalarTowerDivision

/-!
# Compatible parameter division on the original homogeneous tower

The geometric lifting, kernel and annihilator theorems supply the three
hypotheses of scalar tower division over the actual power-series base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- The actual complete-base homogeneous transition has the parameter annihilator kernel. -/
theorem boundarySeriesDegree_annihilator (m d : ℕ)
    (s : boundarySeriesDegree K n h (m + 1) d) :
    (PowerSeries.X : PowerSeries K) • s = 0 ↔
      boundarySeriesDegreeTransition K n h m d s = 0 := by
  rw [Subtype.ext_iff, Subtype.ext_iff, boundarySeriesDegree_smul_val]
  exact boundaryGrade_parameter_annihilator K n h m d s

variable [NeZero n]

/-- One bound gives surjectivity and the scalar-power kernel on the actual linear tower. -/
theorem boundarySeriesDegree_uniformExact : ∃ N : ℕ, ∀ d ≥ N,
    (∀ m, Function.Surjective (boundarySeriesDegreeTransition K n h m d)) ∧
    (∀ m (s : boundarySeriesDegree K n h (m + 1) d),
      boundarySeriesDegreeTransition K n h m d s = 0 ↔
        ∃ t, (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s) := by
  obtain ⟨A, hA⟩ := boundarySections_uniformSurjective K n h
  obtain ⟨B, hB⟩ := boundaryGrade_uniformScalarKernel K n h
  refine ⟨max A B, fun d hd ↦ ⟨?_, ?_⟩⟩
  · intro m
    exact boundaryDegreeTransition_surjective K n h m d (hA d (le_trans (le_max_left _ _) hd) m)
  · intro m s
    rw [Subtype.ext_iff]
    change boundarySectionsMap K n h (homOfLE (Nat.le_succ m)) s.val = 0 ↔ _
    rw [hB d (le_trans (le_max_right _ _) hd) m s]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, Subtype.ext ?_⟩
      exact (boundarySeriesDegree_parameterPower_val K n h (m + 1) d (m + 1) t).trans ht
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      exact (boundarySeriesDegree_parameterPower_val K n h (m + 1) d (m + 1) t).symm.trans
        (congrArg Subtype.val ht)

/-- Vanishing at an original stage admits a compatible division by its parameter power. -/
theorem boundarySeriesDegree_uniformPowerDivision : ∃ N : ℕ, ∀ d ≥ N,
    ∀ m (s : ∀ a, boundarySeriesDegree K n h a d),
      ScalarTowerDivision.Compatible (fun a ↦ boundarySeriesDegreeTransition K n h a d) s →
      s m = 0 → ∃ t : ∀ a, boundarySeriesDegree K n h a d,
        ScalarTowerDivision.Compatible (fun a ↦ boundarySeriesDegreeTransition K n h a d) t ∧
        ∀ a, (PowerSeries.X : PowerSeries K) ^ (m + 1) • t a = s a := by
  obtain ⟨N, hN⟩ := boundarySeriesDegree_uniformExact K n h
  refine ⟨N, fun d hd m s hs hz ↦ ?_⟩
  exact ScalarTowerDivision.exists_compatible_power_division PowerSeries.X
    (fun a ↦ boundarySeriesDegreeTransition K n h a d) (hN d hd).1 (hN d hd).2
    (fun a ↦ boundarySeriesDegree_annihilator K n h a d) m s hs hz

end FLT.Mazur.PolygonInfinitesimalStages
