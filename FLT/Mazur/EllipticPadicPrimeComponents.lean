/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PadicValuationArithmetic
public import FLT.Mazur.PrimeTorsionComponentsAtTwo
public import FLT.Mazur.PrimeTorsionComponentsAtThree
public import FLT.Mazur.PrimeTorsionComponentsAtPrime

/-!
# Component conclusions over the actual rational p-adic rings

The finite residue field and unramifiedness inputs are proved for the original
rings of p-adic integers. At two and three reduction is split multiplicative;
at the torsion prime the bad-reduction branch has injective split components.
Every statement retains the same specified generator.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

/-- At two or three, the actual p-adic cyclic subgroup injects into split components. -/
theorem padic_prime_torsion_components_small (q : ℕ) [Fact q.Prime]
    (hq : q = 2 ∨ q = 3) (W : WeierstrassCurve (padicIntegerSubring q))
    [(W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).IsElliptic]
    [IsMinimal (padicIntegerSubring q) (W.map (algebraMap (padicIntegerSubring q) ℚ_[q]))]
    (p : ℕ) [Fact p.Prime] (hp17 : 17 ≤ p)
    (P : (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).toProjective.Point)
    (hne : P ≠ 0) (hP : p • P = 0) :
    (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasMultiplicativeReduction
        (padicIntegerSubring q) ∧
      ¬ SmoothReduction (padicIntegerSubring q) W P ∧
      (W.nodePoly.map (residue (padicIntegerSubring q))).Splits ∧
      Function.Injective (ellipticSubgroupComponentHom
        (padicIntegerSubring q) W (AddSubgroup.zmultiples P)) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal (padicIntegerSubring q) ^ n ∧
        W.Δ ∉ maximalIdeal (padicIntegerSubring q) ^ (n + 1) ∧ p ∣ n := by
  rcases hq with rfl | rfl
  · exact prime_torsion_components_at_two _ W (padicIntegerSubring_residue_card 2) p hp17 P hne hP
  · exact prime_torsion_components_at_three _ W (padicIntegerSubring_residue_card 3) p hp17 P hne hP

/-- At the actual torsion-prime place, bad reduction has split injective prime components. -/
theorem padic_prime_torsion_components_at_prime (p : ℕ) [Fact p.Prime] (hp17 : 17 ≤ p)
    (W : WeierstrassCurve (padicIntegerSubring p))
    [(W.map (algebraMap (padicIntegerSubring p) ℚ_[p])).IsElliptic]
    [IsMinimal (padicIntegerSubring p) (W.map (algebraMap (padicIntegerSubring p) ℚ_[p]))]
    (hd : W.Δ ∈ maximalIdeal (padicIntegerSubring p))
    (P : (W.map (algebraMap (padicIntegerSubring p) ℚ_[p])).toProjective.Point)
    (hne : P ≠ 0) (hP : p • P = 0) :
    IsUnit W.c₄ ∧ ¬ SmoothReduction (padicIntegerSubring p) W P ∧
      (W.nodePoly.map (residue (padicIntegerSubring p))).Splits ∧
      Function.Injective (ellipticSubgroupComponentHom
        (padicIntegerSubring p) W (AddSubgroup.zmultiples P)) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal (padicIntegerSubring p) ^ n ∧
        W.Δ ∉ maximalIdeal (padicIntegerSubring p) ^ (n + 1) ∧ p ∣ n := by
  exact prime_torsion_components_at_prime _ W p
    (padicIntegerSubring_irreducible_prime p) hp17 hd P hne hP

end FLT.Mazur
