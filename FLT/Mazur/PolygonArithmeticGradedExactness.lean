/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticGradedParameter
public import FLT.Mazur.PolygonArithmeticScalarExactness

/-!
# Actual homogeneous adjacent kernels over the integral coefficient base

Above one uniform degree bound, an actual homogeneous section restricts to
zero exactly when it is a last-parameter-power multiple of another section
of the same degree. The multiplication is that of the original graded ring.
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
/-- Homogeneous evaluation kernels are exactly homogeneous integral-base parameter multiples. -/
theorem boundaryGrade_uniformScalarKernel : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : grade (boundaryLine A π (m + 1) n h) ⊤ d,
      boundarySectionsMap A π n h (homOfLE (Nat.le_succ m)) s.val = 0 ↔
        ∃ t : grade (boundaryLine A π (m + 1) n h) ⊤ d,
          boundaryIntegralScalars A π n h (m + 1) π ^ (m + 1) * t.val = s.val := by
  obtain ⟨N, hN⟩ := boundarySections_uniformScalarExact A π hne n h hgen
  refine ⟨N, fun d hd m s ↦ ?_⟩
  obtain ⟨s, ⟨u, rfl⟩⟩ := s
  change boundarySectionsMap A π n h (homOfLE (Nat.le_succ m))
      (of (boundaryLine A π (m + 1) n h) ⊤ d u) = 0 ↔ _
  rw [boundarySectionsMap_adjacent_ringHom, SectionGradedLinePullback.ringHom_of_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (hN d hd m u).mp hz
    refine ⟨⟨of (boundaryLine A π (m + 1) n h) ⊤ d v, ⟨v, rfl⟩⟩, ?_⟩
    exact (boundaryIntegralScalars_power_of A π n h (m + 1) (m + 1) d v).trans
      (congrArg (of (boundaryLine A π (m + 1) n h) ⊤ d) hv)
  · rintro ⟨⟨t, ⟨v, rfl⟩⟩, ht⟩
    rw [boundaryIntegralScalars_power_of] at ht
    have hv : stageParameterSection A π (m + 1) n h ^ (m + 1) • v = u :=
      DirectSum.of_injective d ht
    exact (hN d hd m u).mpr ⟨v, hv⟩

end FLT.Mazur.PolygonArithmeticStages
