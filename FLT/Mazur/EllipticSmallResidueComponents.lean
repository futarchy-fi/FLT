/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmallResidueTorsion
public import FLT.Mazur.EllipticGoodReductionDiscriminant
public import FLT.Mazur.EllipticGoodComponent
public import FLT.Mazur.EllipticPrimeSubgroupComponents
public import FLT.Mazur.EllipticUnitInvariantsReduction

/-!
# Split components over a small residue field

The original nonzero prime-torsion point lies outside smooth reduction. Good,
additive and nonsplit multiplicative reduction are thereby excluded on the
minimal equation. Its actual cyclic subgroup injects into the split component
quotient, and the prime divides the positive discriminant depth.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)] [(W.map (algebraMap A K)).IsElliptic]
  [IsMinimal A (W.map (algebraMap A K))]

/-- Small residue fields force actual split multiplicative components for the given generator. -/
theorem prime_components_of_small_residue
    (q p : ℕ) [CharP (ResidueField A) q] [Fact p.Prime] (hp4 : 4 < p)
    (hqp : ¬ q ∣ p) (hcard : Nat.card (ResidueField A) ^ 2 + 1 < p)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hne : P ≠ 0) (hP : p • P = 0) :
    (W.map (algebraMap A K)).HasMultiplicativeReduction A ∧
      ¬ SmoothReduction A W P ∧ (W.nodePoly.map (residue A)).Splits ∧
      Function.Injective (ellipticSubgroupComponentHom A W (AddSubgroup.zmultiples P)) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧
        W.Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n := by
  have hns := not_smoothReduction_prime_torsion_of_residue_card_bound A W q p Fact.out
    hqp hcard P hne hP
  have hd : W.Δ ∈ maximalIdeal A := by
    intro hu
    let _ : W.IsElliptic := ⟨hu⟩
    exact hns (smoothReduction_of_isElliptic A W P)
  have hu : IsUnit W.c₄ := by
    by_contra hc
    exact hns (smoothReduction_prime_torsion_minimalAdditive A W hd hc Fact.out hp4 P hP)
  have hs : (W.nodePoly.map (residue A)).Splits := by
    by_contra hn
    exact hns (smoothReduction_prime_torsion_nonsplitNodal A W hd hu hn Fact.out
      (by omega) P hP)
  have hc : Nat.card (AddSubgroup.zmultiples P) = p := by
    rw [Nat.card_zmultiples, addOrderOf_eq_prime hP hne]
  have hH : ¬ AddSubgroup.zmultiples P ≤ ellipticE0 A W := by
    intro h
    exact hns (h (AddSubgroup.mem_zmultiples P))
  have hr := (good_or_multiplicative_of_unit_invariants (K := K) W (Or.inr hu)).resolve_left
    (fun hg => by
      let _ := hg
      exact hd (isUnit_discriminant_of_hasGoodReduction (K := K) W))
  exact ⟨hr, hns, hs,
    (primeSubgroup_smooth_or_component_injective A W _ p hc).resolve_left hH,
    primeSubgroup_splitNode_depth_dvd A W _ p hc hd hu hs hH⟩

end FLT.Mazur
