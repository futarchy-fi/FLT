/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicIntegerCompact
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Locality of integral closures over a complete DVR

The normalized valuation equips the base fraction field with a complete
nonarchimedean norm. The spectral norm then proves that the integral closure
in a finite extension is a valuation ring, hence local.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing
open scoped WithZero

variable (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsAdicComplete (maximalIdeal R) R]

include K in
/-- The integral closure in a finite extension of a complete DVR fraction field is local. -/
theorem finiteExtension_integralClosure_local : IsLocalRing (integralClosure R L) := by
  let := dvrAdicValued R K
  let : (Valued.v : Valuation K ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (v := (dvrPrime R).valuation K)
      (by norm_num : (1 : NNReal) < 2)
  let := Valued.toNontriviallyNormedField K ℤᵐ⁰
  let : CompleteSpace K := adicFractionFieldComplete R K
  have hint (x : L) (hx : spectralNorm K L x ≤ 1) : IsIntegral R x := by
    rw [spectralNorm, spectralValue_le_one_iff
      (minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) x))] at hx
    have hlift : minpoly K x ∈ Polynomial.lifts (algebraMap R K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      have hn : (dvrPrime R).valuation K ((minpoly K x).coeff n) ≤ 1 :=
        (Valued.toNormedField.norm_le_one_iff).mp (hx n)
      exact (Set.ext_iff.mp (dvrAdicValued_integers R K) _).mpr hn
    obtain ⟨f, hf, _, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
      (minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) x))
    refine ⟨f, hm, ?_⟩
    change Polynomial.aeval x f = 0
    rw [← Polynomial.aeval_map_algebraMap K, hf]
    exact minpoly.aeval K x
  let V : ValuationSubring L :=
    { toSubring := (integralClosure R L).toSubring
      mem_or_inv_mem' := fun x => by
        let := spectralNorm.nontriviallyNormedField K L
        change IsIntegral R x ∨ IsIntegral R x⁻¹
        by_cases hx : spectralNorm K L x ≤ 1
        · exact Or.inl (hint x hx)
        · apply Or.inr
          apply hint
          change ‖x⁻¹‖ ≤ 1
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hx)) }
  exact inferInstanceAs (IsLocalRing V)

end LocalClassFieldTheory
