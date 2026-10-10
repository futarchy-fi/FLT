/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PadicValuationArithmetic
public import FLT.Mazur.PrimeTorsionSemistabilityAtPrime
public import FLT.Mazur.PrimeTorsionSemistabilityAway

/-!
# Semistability at every rational p-adic place

The residue-prime case uses the actual unramified scaling construction. At
all other primes, the prime-to-residue component argument applies. Thus every
minimal integral p-adic equation with a nonzero point of prime order at least
seventeen is semistable, with no arithmetic hypotheses left to supply.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

/-- At every rational prime, a minimal integral model carrying large prime torsion is semistable. -/
theorem padic_semistable_of_prime_torsion (q : ℕ) [Fact q.Prime]
    (W : WeierstrassCurve (padicIntegerSubring q))
    [(W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic]
    [IsMinimal (padicIntegerSubring q) (W.map (algebraMap (padicIntegerSubring q) ℚ_[q]))]
    (p : ℕ) [Fact p.Prime] (hp17 : 17 ≤ p)
    (P : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).toProjective.Point)
    (hne : P ≠ 0) (hP : p • P = 0) :
    (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasGoodReduction
        (padicIntegerSubring q) ∨
      (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasMultiplicativeReduction
        (padicIntegerSubring q) := by
  by_cases hqp : q = p
  · subst p
    exact semistable_of_prime_torsion_unramified _ W q
      (padicIntegerSubring_irreducible_prime q) hp17 P hne hP
  · apply good_or_multiplicative_of_prime_torsion _ W q p Fact.out (by omega) _ P hne hP
    rwa [Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)]

/-- Any minimal generic equation carrying large prime torsion is semistable at its p-adic place. -/
theorem padic_minimal_semistable_of_large_prime_point (q : ℕ) [Fact q.Prime]
    (E : WeierstrassCurve ℚ_[q]) [E.IsElliptic] [IsMinimal (padicIntegerSubring q) E]
    (p : ℕ) [Fact p.Prime] (hp17 : 17 ≤ p)
    (hP : ∃ P : E.toProjective.Point, P ≠ 0 ∧ p • P = 0) :
    E.HasGoodReduction (padicIntegerSubring q) ∨
      E.HasMultiplicativeReduction (padicIntegerSubring q) := by
  let W := E.integralModel (padicIntegerSubring q)
  have he : W.map (algebraMap (padicIntegerSubring q) ℚ_[q]) = E :=
    baseChange_integralModel_eq _ E
  let _ : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic := he.symm ▸ inferInstance
  let _ : IsMinimal (padicIntegerSubring q)
      (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])) := he.symm ▸ inferInstance
  have ht : ∃ P : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).toProjective.Point,
      P ≠ 0 ∧ p • P = 0 := he.symm ▸ hP
  obtain ⟨P, hne, hn⟩ := ht
  simpa only [he] using padic_semistable_of_prime_torsion q W p hp17 P hne hn

end FLT.Mazur
