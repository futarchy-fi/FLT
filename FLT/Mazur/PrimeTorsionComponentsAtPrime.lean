/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrimeTorsionSemistabilityAtPrime
public import FLT.Mazur.EllipticSmallRamificationComponents

/-!
# The original prime-torsion component at the torsion prime

At an unramified residue prime at least seventeen, the original minimal equation
is semistable. If its discriminant is a nonunit, the exact cyclic subgroup
injects into split components and the prime divides the positive discriminant
depth. The generator itself lies outside the identity component.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)] [(W.map (algebraMap A K)).IsElliptic]
  [IsMinimal A (W.map (algebraMap A K))]

/-- At the unramified torsion prime, bad reduction has split injective prime components. -/
theorem prime_torsion_components_at_prime
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hp : Irreducible (p : A)) (hp17 : 17 ≤ p) (hd : W.Δ ∈ maximalIdeal A)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hne : P ≠ 0) (hP : p • P = 0) :
    IsUnit W.c₄ ∧ ¬ SmoothReduction A W P ∧ (W.nodePoly.map (residue A)).Splits ∧
      Function.Injective (ellipticSubgroupComponentHom A W (AddSubgroup.zmultiples P)) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧
        W.Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n := by
  have hu := (unit_invariants_of_prime_torsion_unramified A W p hp hp17 P hne hP).resolve_left hd
  have he : RaynaudParameters.order (p : A) < p - 1 := by
    rw [RaynaudParameters.order, IsDiscreteValuationRing.addVal_uniformizer hp]
    norm_num
    omega
  have hc : Nat.card (AddSubgroup.zmultiples P) = p := by
    rw [Nat.card_zmultiples, addOrderOf_eq_prime hP hne]
  obtain ⟨hs, hi, hn⟩ := primeSubgroup_split_components_small_ramification A W p hp.ne_zero
    he (AddSubgroup.zmultiples P) hc hd hu (by omega)
  have hns : ¬ SmoothReduction A W P := by
    intro hsm
    let Q : AddSubgroup.zmultiples P := ⟨P, AddSubgroup.mem_zmultiples P⟩
    have hz : ellipticSubgroupComponentHom A W (AddSubgroup.zmultiples P) Q = 0 :=
      (ellipticComponentHom_eq_zero A W P).mpr hsm
    have hQ := hi (hz.trans (map_zero _).symm)
    exact hne (congrArg (AddSubgroup.zmultiples P).subtype hQ)
  exact ⟨hu, hns, hs, hi, hn⟩

end FLT.Mazur
