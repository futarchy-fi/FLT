/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralDegreeTwoComparison

/-!
# Normalizing continuous two-cocycles

Subtracting the differential of a constant one-cochain gives a normalized
cocycle, without changing whether the original cocycle is a boundary.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology GaloisRepresentation.Extensions

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- Remove the constant-cochain boundary from a continuous two-cochain. -/
def normalizedTwoCochain (c : C(G × G, M)) : C(G × G, M) :=
  ⟨fun z => c z - z.1 • c (1, 1), c.continuous.sub (continuous_fst.smul continuous_const)⟩

/-- Normalization preserves the cocycle equation. -/
theorem normalizedTwoCochain_isCocycle (c : C(G × G, M)) (hc : IsCocycle₂ c) :
    IsCocycle₂ (normalizedTwoCochain c) := by
  intro g h j
  change c (g * h, j) - (g * h) • c (1, 1) + (c (g, h) - g • c (1, 1)) =
    g • (c (h, j) - h • c (1, 1)) + (c (g, h * j) - g • c (1, 1))
  rw [smul_sub, ← mul_smul]
  calc
    _ = (c (g * h, j) + c (g, h)) - (g * h) • c (1, 1) - g • c (1, 1) := by abel
    _ = (g • c (h, j) + c (g, h * j)) - (g * h) • c (1, 1) - g • c (1, 1) := by
      rw [hc]
    _ = _ := by abel

/-- The normalized cocycle vanishes when the first argument is the identity. -/
theorem normalizedTwoCochain_one_left (c : C(G × G, M)) (hc : IsCocycle₂ c) (g : G) :
    normalizedTwoCochain c (1, g) = 0 := by
  change c (1, g) - (1 : G) • c (1, 1) = 0
  rw [map_one_fst_of_isCocycle₂ hc, one_smul, sub_self]

/-- The normalized cocycle vanishes when the second argument is the identity. -/
theorem normalizedTwoCochain_one_right (c : C(G × G, M)) (hc : IsCocycle₂ c) (g : G) :
    normalizedTwoCochain c (g, 1) = 0 := by
  change c (g, 1) - g • c (1, 1) = 0
  rw [map_one_snd_of_isCocycle₂ hc, sub_self]

/-- Normalization preserves and reflects continuous boundaries. -/
theorem normalizedTwoCochain_boundary_iff (c : C(G × G, M)) :
    ContinuousIsCoboundaryTwo (normalizedTwoCochain c) ↔ ContinuousIsCoboundaryTwo c := by
  apply continuousCoboundaryTwo_difference_iff c (normalizedTwoCochain c)
    (ContinuousMap.const G (-c (1, 1)))
  intro g h
  change g • (-c (1, 1)) - -c (1, 1) + -c (1, 1) =
    (c (g, h) - g • c (1, 1)) - c (g, h)
  rw [smul_neg]
  abel

end LocalClassFieldTheory
