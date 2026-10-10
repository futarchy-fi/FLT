/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmallResidueComponents

/-!
# The original prime-torsion component at 3

For a residue field with 3 elements and a prime at least seventeen, the original
nonzero point lies outside E₀. Its cyclic subgroup injects into split
multiplicative components, and the prime divides the discriminant depth.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)] [CharP (ResidueField A) 3]
  [(W.map (algebraMap A K)).IsElliptic] [IsMinimal A (W.map (algebraMap A K))]

/-- Split multiplicative reduction and injective components for the original prime point at 3. -/
theorem prime_torsion_components_at_three
    (hcard : Nat.card (ResidueField A) = 3) (p : ℕ) [Fact p.Prime] (hp17 : 17 ≤ p)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hne : P ≠ 0) (hP : p • P = 0) :
    (W.map (algebraMap A K)).HasMultiplicativeReduction A ∧
      ¬ SmoothReduction A W P ∧ (W.nodePoly.map (residue A)).Splits ∧
      Function.Injective (ellipticSubgroupComponentHom A W (AddSubgroup.zmultiples P)) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧
        W.Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n := by
  apply prime_components_of_small_residue A W 3 p (by omega) _ _ P hne hP
  · intro h
    have hd := (Fact.out : p.Prime).eq_one_or_self_of_dvd 3 h
    omega
  · rw [hcard]
    norm_num
    omega

end FLT.Mazur
