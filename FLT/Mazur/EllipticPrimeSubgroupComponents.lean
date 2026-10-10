/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticPrimeTorsionComponents
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Prime subgroups and the actual component quotient

A prime-order subgroup either lies entirely in smooth reduction or injects
into the actual rational component quotient. Nonsplit nodes force the first
case; at split nodes the second case forces p to divide the discriminant depth.
These statements do not put a group structure on a nodal cubic closure.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)
  (p : ℕ) [Fact p.Prime] (hc : Nat.card H = p)

/-- The original component homomorphism restricted to the given subgroup. -/
def ellipticSubgroupComponentHom : H →+ EllipticComponentQuotient A W :=
  (ellipticComponentHom A W).comp H.subtype

include hc in
/-- Prime order gives the precise smooth-containment or component-injection alternative. -/
theorem primeSubgroup_smooth_or_component_injective :
    H ≤ ellipticE0 A W ∨ Function.Injective (ellipticSubgroupComponentHom A W H) := by
  let _ : Fact (Nat.card H).Prime := ⟨hc.symm ▸ (Fact.out : p.Prime)⟩
  rcases (ellipticSubgroupComponentHom A W H).ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact Or.inr ((ellipticSubgroupComponentHom A W H).ker_eq_bot_iff.mp h)
  · left
    intro P hP
    apply (ellipticComponentHom_eq_zero A W P).mp
    have hm : (⟨P, hP⟩ : H) ∈ (ellipticSubgroupComponentHom A W H).ker := by
      rw [h]
      trivial
    exact hm

include hc in
/-- Failure of smooth containment forces the original prime into the component order. -/
theorem prime_dvd_component_card_of_not_smooth (hH : ¬ H ≤ ellipticE0 A W) :
    p ∣ Nat.card (EllipticComponentQuotient A W) := by
  rw [← hc]
  exact AddSubgroup.card_dvd_of_injective (ellipticSubgroupComponentHom A W H)
    ((primeSubgroup_smooth_or_component_injective A W H p hc).resolve_left hH)

variable [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  [(W.map (algebraMap A K)).IsElliptic]

include hc in
/-- Every point of an odd prime-order subgroup has smooth reduction at a nonsplit node. -/
theorem primeSubgroup_le_ellipticE0_nonsplitNodal
    (hΔ : W.Δ ∈ maximalIdeal A) (hu : IsUnit W.c₄)
    (hns : ¬ (W.nodePoly.map (residue A)).Splits) (hp2 : 2 < p) :
    H ≤ ellipticE0 A W := by
  intro P hP
  apply smoothReduction_prime_torsion_nonsplitNodal A W hΔ hu hns Fact.out hp2
  have hk : Nat.card H • (⟨P, hP⟩ : H) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard _)
  have h := congrArg H.subtype hk
  simpa only [map_nsmul, map_zero, AddSubgroup.subtype_apply, hc] using h

include hc in
/-- A split prime subgroup outside smooth reduction forces p-divisible discriminant depth. -/
theorem primeSubgroup_splitNode_depth_dvd
    (hΔ : W.Δ ∈ maximalIdeal A) (hu : IsUnit W.c₄)
    (hs : (W.nodePoly.map (residue A)).Splits) (hH : ¬ H ≤ ellipticE0 A W) :
    ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧
      W.Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n := by
  obtain ⟨_, _, n, hn, hd, hd', hc'⟩ := splitNode_components A W hΔ hu hs
  exact ⟨n, hn, hd, hd',
    (prime_dvd_component_card_of_not_smooth A W H p hc hH).trans hc'⟩

end FLT.Mazur
