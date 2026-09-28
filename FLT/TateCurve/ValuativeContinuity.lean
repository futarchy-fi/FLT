/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange

/-!
# Continuity of valuative local-field embeddings

Powers of a nonzero element of the open unit disc give arbitrarily small radii
in the target field. Preservation of the valuative relation then proves continuity.
-/

@[expose] public section

open ValuativeRel Filter
open scoped Topology

namespace TateCurve

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- A valuative local-field embedding is continuous when the source has a nonzero
element in the open unit disc. -/
theorem continuous_algebraMap_of_valuation_lt_one {q : K} (hq0 : q ≠ 0)
    (hq : valuation K q < 1) : Continuous (algebraMap K L) := by
  have hpow := tendsto_pow_nhds_zero (valuation_algebraMap_lt_one (l := L) hq)
  apply continuous_iff_continuousAt.mpr
  intro x
  apply ((IsValuativeTopology.hasBasis_nhds x).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds (algebraMap K L x))).mpr
  intro γ _
  have hmem : {y : L | valuation L y < γ} ∈ 𝓝 (0 : L) :=
    (IsValuativeTopology.hasBasis_nhds_zero L).mem_of_mem (i := γ) trivial
  obtain ⟨n, hn⟩ := (hpow.eventually hmem).exists
  refine ⟨Units.mk0 (valuation K (q ^ n))
    ((valuation K).ne_zero_iff.mpr (pow_ne_zero n hq0)), trivial, ?_⟩
  intro y hy
  change valuation K (y - x) < valuation K (q ^ n) at hy
  change valuation L (algebraMap K L y - algebraMap K L x) < γ
  rw [← map_sub]
  have hlt := (ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := L)) hy
  simp only [ValuativeExtension.mapValueGroupWithZero_valuation] at hlt
  exact hlt.trans (by simpa only [map_pow] using hn)

end TateCurve
