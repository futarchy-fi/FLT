/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.InflationKernelCorrection

/-!
# Inflation reflects continuous two-boundaries

The kernel Hilbert 90 condition, together with the actual identification of
invariant coefficients, descends any continuous bounding cochain. No
injectivity on cohomology is assumed.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology GaloisRepresentation.Extensions

variable {G H M P : Type*} [Group G] [Group H]
  [AddCommGroup M] [AddCommGroup P] [DistribMulAction H M] [DistribMulAction G P]
  [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace P] [DiscreteTopology P]
  [ContinuousSMul G P] [ContinuousSMul H M]

/-- Any continuous boundary of an inflated cocycle descends through the quotient. -/
theorem continuousInflation_boundary_descends (f : G →* H) (hf : Topology.IsQuotientMap f)
    (i : M →+ P) (hi : Function.Injective i) (heq : ∀ g m, i (f g • m) = g • i m)
    (hfix : ∀ p : P, (∀ n, f n = 1 → n • p = p) → ∃ m, i m = p)
    (hker : ∀ z : ContinuousCocycle f.ker P, ∃ a : P, ∀ n, z.val n = n • a - a)
    (c : C(H × H, M)) (hc : IsCocycle₂ c) (b : C(G, P))
    (hb : ∀ g h, g • b h - b (g * h) + b g = i (c (f g, f h))) :
    ContinuousIsCoboundaryTwo c := by
  let d := b - ContinuousMap.const G (i (c (1, 1)))
  have hd : ∀ g h, g • d h - d (g * h) + d g =
      i (normalizedTwoCochain c (f g, f h)) := by
    intro g h
    change g • (b h - i (c (1, 1))) - (b (g * h) - i (c (1, 1))) +
      (b g - i (c (1, 1))) = i (c (f g, f h) - f g • c (1, 1))
    rw [smul_sub, map_sub, heq]
    calc
      _ = (g • b h - b (g * h) + b g) - g • i (c (1, 1)) := by abel
      _ = _ := by rw [hb]
  exact (normalizedTwoCochain_boundary_iff c).mp
    (normalized_inflationBoundary_descends f i hf hi heq hfix hker
      (normalizedTwoCochain c) (normalizedTwoCochain_one_right c hc)
      (normalizedTwoCochain_one_left c hc) d hd)

end LocalClassFieldTheory
