/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAdditiveTorsionExclusion

/-!
# Large prime torsion gives semistability away from its order

On a minimal equation over a complete DVR with perfect residue field,
nonzero p-torsion for p>4 forces good or multiplicative reduction whenever
the residue characteristic does not divide p. The conclusion uses Mathlib's
actual reduction predicates. No assertion at the torsion prime is made.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] (A : ValuationSubring K)
variable [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
variable [PerfectField (ResidueField A)]

/-- A minimal integral equation with nonzero large prime-to-residue torsion is semistable. -/
theorem good_or_multiplicative_of_prime_torsion (W : WeierstrassCurve A)
    [(W.map (algebraMap A K)).IsElliptic] [IsMinimal A (W.map (algebraMap A K))]
    (q p : ℕ) [CharP (ResidueField A) q] (hp : p.Prime) (hp4 : 4 < p)
    (hqp : ¬ q ∣ p) (P : (W.map (algebraMap A K)).toProjective.Point)
    (hne : P ≠ 0) (hP : p • P = 0) :
    (W.map (algebraMap A K)).HasGoodReduction A ∨
      (W.map (algebraMap A K)).HasMultiplicativeReduction A := by
  by_cases hΔ : W.Δ ∈ maximalIdeal A
  · right
    have hc := isUnit_c₄_of_prime_torsion A W hΔ q p hp hp4 hqp P hne hP
    exact { badReduction := by
              rw [map_Δ]
              exact (valuation_lt_one_iff_mem _ _).mpr hΔ
            multiplicativeReduction := by
              rw [map_c₄, valuation_eq_one_iff_notMem]
              intro h
              change W.c₄ ∈ IsLocalRing.maximalIdeal A at h
              have hnu : ¬ IsUnit W.c₄ := by
                simpa only [mem_maximalIdeal, mem_nonunits_iff] using h
              exact hnu hc }
  · left
    exact { goodReduction := by rw [map_Δ, valuation_eq_one_iff_notMem]; exact hΔ }

/-- Semistability away from p for any minimal generic equation with a nonzero p-torsion point. -/
theorem minimal_semistable_of_large_prime_point (E : WeierstrassCurve K)
    [E.IsElliptic] [IsMinimal A E] (q p : ℕ) [CharP (ResidueField A) q]
    (hp : p.Prime) (hp4 : 4 < p) (hqp : ¬ q ∣ p)
    (hP : ∃ P : E.toProjective.Point, P ≠ 0 ∧ p • P = 0) :
    E.HasGoodReduction A ∨ E.HasMultiplicativeReduction A := by
  let W := E.integralModel A
  have he : W.map (algebraMap A K) = E := baseChange_integralModel_eq A E
  have : (W.map (algebraMap A K)).IsElliptic := he.symm ▸ inferInstance
  have : IsMinimal A (W.map (algebraMap A K)) := he.symm ▸ inferInstance
  have hP' : ∃ P : (W.map (algebraMap A K)).toProjective.Point, P ≠ 0 ∧ p • P = 0 := by
    exact he.symm ▸ hP
  obtain ⟨P, hne, hP⟩ := hP'
  simpa only [he] using good_or_multiplicative_of_prime_torsion A W q p hp hp4 hqp P hne hP

/-- In particular, a minimal equation carrying large prime torsion cannot have additive reduction
away from that prime. -/
theorem not_additive_of_large_prime_point (E : WeierstrassCurve K)
    [E.IsElliptic] [IsMinimal A E] (q p : ℕ) [CharP (ResidueField A) q]
    (hp : p.Prime) (hp4 : 4 < p) (hqp : ¬ q ∣ p)
    (hP : ∃ P : E.toProjective.Point, P ≠ 0 ∧ p • P = 0) :
    ¬ E.HasAdditiveReduction A := by
  rcases minimal_semistable_of_large_prime_point A E q p hp hp4 hqp hP with h | h
  · exact h.not_hasAdditiveReduction
  · exact h.not_hasAdditiveReduction

end FLT.Mazur
