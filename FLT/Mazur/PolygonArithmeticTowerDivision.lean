/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticIntegralDegree
public import FLT.Mazur.PolygonArithmeticGradedExactness
public import FLT.Mazur.ScalarTowerDivision

/-!
# Compatible parameter division on the original homogeneous tower

The geometric lifting, kernel and annihilator theorems supply the three
hypotheses of scalar tower division over the original integral base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (n : ℕ) (h : 2 ≤ n)

include hne in
/-- The actual integral-base homogeneous transition has the parameter annihilator kernel. -/
theorem boundaryIntegralDegree_annihilator (m d : ℕ)
    (s : boundaryIntegralDegree A π n h (m + 1) d) :
    π • s = 0 ↔
      boundaryIntegralDegreeTransition A π n h m d s = 0 := by
  rw [Subtype.ext_iff, Subtype.ext_iff, boundaryIntegralDegree_smul_val]
  exact boundaryGrade_parameter_annihilator A π n h hne m d s

variable [IsLocalRing A] [NeZero n]
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hne hgen in
/-- One bound gives surjectivity and the scalar-power kernel on the actual linear tower. -/
theorem boundaryIntegralDegree_uniformExact : ∃ N : ℕ, ∀ d ≥ N,
    (∀ m, Function.Surjective (boundaryIntegralDegreeTransition A π n h m d)) ∧
    (∀ m (s : boundaryIntegralDegree A π n h (m + 1) d),
      boundaryIntegralDegreeTransition A π n h m d s = 0 ↔
        ∃ t, π ^ (m + 1) • t = s) := by
  obtain ⟨N₀, hA⟩ := boundarySections_uniformSurjective A π hne hgen n h
  obtain ⟨N₁, hB⟩ := boundaryGrade_uniformScalarKernel A π hne hgen n h
  refine ⟨max N₀ N₁, fun d hd ↦ ⟨?_, ?_⟩⟩
  · intro m
    exact boundaryDegreeTransition_surjective A π n h m d (hA d (le_trans (le_max_left _ _) hd) m)
  · intro m s
    rw [Subtype.ext_iff]
    change boundarySectionsMap A π n h (homOfLE (Nat.le_succ m)) s.val = 0 ↔ _
    rw [hB d (le_trans (le_max_right _ _) hd) m s]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, Subtype.ext ?_⟩
      exact (boundaryIntegralDegree_parameterPower_val A π n h (m + 1) d (m + 1) t).trans ht
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      exact (boundaryIntegralDegree_parameterPower_val A π n h (m + 1) d (m + 1) t).symm.trans
        (congrArg Subtype.val ht)

include hne hgen in
/-- Vanishing at an original stage admits a compatible division by its parameter power. -/
theorem boundaryIntegralDegree_uniformPowerDivision : ∃ N : ℕ, ∀ d ≥ N,
    ∀ m (s : ∀ a, boundaryIntegralDegree A π n h a d),
      ScalarTowerDivision.Compatible (fun a ↦ boundaryIntegralDegreeTransition A π n h a d) s →
      s m = 0 → ∃ t : ∀ a, boundaryIntegralDegree A π n h a d,
        ScalarTowerDivision.Compatible (fun a ↦ boundaryIntegralDegreeTransition A π n h a d) t ∧
        ∀ a, π ^ (m + 1) • t a = s a := by
  obtain ⟨N, hN⟩ := boundaryIntegralDegree_uniformExact A π hne n h hgen
  refine ⟨N, fun d hd m s hs hz ↦ ?_⟩
  exact ScalarTowerDivision.exists_compatible_power_division π
    (fun a ↦ boundaryIntegralDegreeTransition A π n h a d) (hN d hd).1 (hN d hd).2
    (fun a ↦ boundaryIntegralDegree_annihilator A π hne n h a d) m s hs hz

end FLT.Mazur.PolygonArithmeticStages
