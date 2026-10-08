/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticUnramifiedAdditiveTorsion
public import FLT.Mazur.EllipticPrimeTorsionComponents

/-!
# Semistability at the large unramified torsion prime

The minimal additive component bound puts the original p-torsion point in E₀.
The constructed short scaling then forces that same point to be zero. Thus a
nonzero point forces good or multiplicative reduction on the original minimal
equation, without a prime-to-residue hypothesis or a nodal closure assumption.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K)
  [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  [PerfectField (ResidueField A)] (W : WeierstrassCurve A)
  [(W.map (algebraMap A K)).IsElliptic] [IsMinimal A (W.map (algebraMap A K))]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
  (hp : Irreducible (p : A)) (hp17 : 17 ≤ p)

include hp hp17

/-- A minimal additive equation has no nonzero p-torsion at an unramified p ≥ 17. -/
theorem prime_torsion_eq_zero_of_minimalAdditive_unramified
    (hd : W.Δ ∈ maximalIdeal A) (hc : W.c₄ ∈ maximalIdeal A)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0) : P = 0 := by
  exact smooth_prime_torsion_eq_zero_of_additive_unramified A p hp hp17 W hd hc P hP
    (smoothReduction_prime_torsion_minimalAdditive A W hd hc Fact.out (by omega) P hP)

/-- Nonzero prime torsion forces semistable invariants on the original minimal equation. -/
theorem unit_invariants_of_prime_torsion_unramified
    (P : (W.map (algebraMap A K)).toProjective.Point) (hne : P ≠ 0)
    (hP : p • P = 0) : IsUnit W.Δ ∨ IsUnit W.c₄ := by
  by_cases hd : IsUnit W.Δ
  · exact Or.inl hd
  · right
    by_contra hc
    exact hne (prime_torsion_eq_zero_of_minimalAdditive_unramified A W p hp hp17 hd hc P hP)

/-- Semistability at the torsion prime, for the exact original equation and point. -/
theorem semistable_of_prime_torsion_unramified
    (P : (W.map (algebraMap A K)).toProjective.Point) (hne : P ≠ 0) (hP : p • P = 0) :
    (W.map (algebraMap A K)).HasGoodReduction A ∨
      (W.map (algebraMap A K)).HasMultiplicativeReduction A := by
  exact good_or_multiplicative_of_unit_invariants W
    (unit_invariants_of_prime_torsion_unramified A W p hp hp17 P hne hP)

end FLT.Mazur
