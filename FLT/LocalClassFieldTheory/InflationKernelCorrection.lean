/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.InflationBoundaryDescent

/-!
# Correcting an inflation boundary on the kernel

Hilbert 90 supplies a principal crossed homomorphism on the kernel.
Subtracting its global principal cochain leaves the boundary unchanged
and makes the bounding cochain vanish on the kernel.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology GaloisRepresentation.Extensions

variable {G H M P : Type*} [Group G] [Group H]
  [AddCommGroup M] [AddCommGroup P] [DistribMulAction H M] [DistribMulAction G P]
  [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace M] [TopologicalSpace P] [DiscreteTopology P]
  [ContinuousSMul G P]
  (f : G →* H) (i : M →+ P)

omit [DistribMulAction H M] [TopologicalSpace H] [TopologicalSpace M] in
/-- A boundary of a normalized inflated cochain can be corrected to vanish on the kernel. -/
theorem exists_kernel_zero_inflationBoundary (c : H × H → M) (hc : c (1, 1) = 0)
    (hker : ∀ z : ContinuousCocycle f.ker P, ∃ a : P, ∀ n, z.val n = n • a - a)
    (b : C(G, P))
    (hb : ∀ g h, g • b h - b (g * h) + b g = i (c (f g, f h))) :
    ∃ d : C(G, P), (∀ n, f n = 1 → d n = 0) ∧
      ∀ g h, g • d h - d (g * h) + d g = i (c (f g, f h)) := by
  let z : ContinuousCocycle f.ker P :=
    ⟨⟨fun n => b n, b.continuous.comp continuous_subtype_val⟩, fun g h => by
      have he := hb g h
      rw [g.property, h.property, hc, map_zero] at he
      change b ((g : G) * h) = (g : G) • b h + b g
      exact (sub_eq_zero.mp (by convert he using 1; abel)).symm⟩
  obtain ⟨a, ha⟩ := hker z
  let d : C(G, P) := b -
    ⟨fun g => g • a - a, (continuous_id.smul continuous_const).sub continuous_const⟩
  refine ⟨d, ?_, ?_⟩
  · intro n hn
    change b n - (n • a - a) = 0
    exact sub_eq_zero.mpr (ha ⟨n, hn⟩)
  · intro g h
    change g • (b h - (h • a - a)) - (b (g * h) - ((g * h) • a - a)) +
      (b g - (g • a - a)) = _
    rw [smul_sub, smul_sub, ← mul_smul]
    calc
      _ = g • b h - b (g * h) + b g := by abel
      _ = _ := hb g h

/-- Normalized inflation reflects continuous boundaries when kernel Hilbert 90 holds. -/
theorem normalized_inflationBoundary_descends (hf : Topology.IsQuotientMap f)
    (hi : Function.Injective i) (heq : ∀ g m, i (f g • m) = g • i m)
    (hfix : ∀ p : P, (∀ n, f n = 1 → n • p = p) → ∃ m, i m = p)
    (hker : ∀ z : ContinuousCocycle f.ker P, ∃ a : P, ∀ n, z.val n = n • a - a)
    (c : C(H × H, M)) (hc0 : ∀ h, c (h, 1) = 0) (hc1 : ∀ h, c (1, h) = 0)
    (b : C(G, P))
    (hb : ∀ g h, g • b h - b (g * h) + b g = i (c (f g, f h))) :
    ContinuousIsCoboundaryTwo c := by
  obtain ⟨d, hd0, hd⟩ := exists_kernel_zero_inflationBoundary f i c (hc0 1) hker b hb
  exact exists_descended_inflationBoundary f i c d hd hd0 hc0 hc1 hf hi heq hfix d.continuous

end LocalClassFieldTheory
