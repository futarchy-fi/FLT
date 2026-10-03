/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralDegreeTwoComparison
public import FLT.LocalClassFieldTheory.IntegralH1Equivalence
public import FLT.LocalClassFieldTheory.KernelCocycleNormalization

/-!
# Equality of explicit continuous H2 classes

Two cocycles represent the same categorical class precisely when their
difference is the differential of a continuous one-cochain.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology GaloisRepresentation.Extensions

variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- Equality of H2 classes detects the continuous bounding cochain of their difference. -/
theorem integralH2Class_eq_iff (c d : C(G × G, M)) (hc : IsCocycle₂ c)
    (hd : IsCocycle₂ d) : integralH2Class (k := ℤ) c hc = integralH2Class (k := ℤ) d hd ↔
      ∃ b : C(G, M), ∀ g h, g • b h - b (g * h) + b g = c (g, h) - d (g, h) := by
  let K := continuousCochains ℤ G M
  let z := continuousTwoCochain (k := ℤ) c
  let w := continuousTwoCochain (k := ℤ) d
  have hz : (K.d 2 ((ComplexShape.up ℕ).next 2)).hom z = 0 := by
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
    exact (continuousTwoCochain_cycle_iff (k := ℤ) c).mpr hc
  have hw : (K.d 2 ((ComplexShape.up ℕ).next 2)).hom w = 0 := by
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
    exact (continuousTwoCochain_cycle_iff (k := ℤ) d).mpr hd
  have hzw : (K.d 2 ((ComplexShape.up ℕ).next 2)).hom (z - w) = 0 := by
    rw [map_sub, hz, hw, sub_self]
  change cochainHomologyClass K 2 z hz = cochainHomologyClass K 2 w hw ↔ _
  rw [← sub_eq_zero, ← cochainHomologyClass_sub K 2 z w hz hw hzw,
    cochainHomologyClass_eq_zero_iff]
  rw [(ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨continuousOneFunction b, fun g h => ?_⟩
    have he := congrArg (fun x : K.X 2 => x.val ![g, h]) hb
    exact (continuous_d_one b g h).symm.trans he
  · rintro ⟨b, hb⟩
    refine ⟨continuousOneCochain b, ?_⟩
    apply Subtype.ext
    funext x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, continuous_d_one]
    exact hb (x 0) (x 1)

end LocalClassFieldTheory
