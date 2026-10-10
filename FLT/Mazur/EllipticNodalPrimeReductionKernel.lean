/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodalResidueTorsion
public import FLT.Mazur.EllipticPrimeSubgroupComponents

/-!
# Prime subgroups in the nodal reduction kernel

In residue characteristic p the smooth reduction of p-torsion on a nodal
equation is zero. Thus a prime subgroup lies in the actual formal kernel E₁,
or injects into the split component quotient with p-divisible discriminant depth.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [Finite (ResidueField A)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
  (hΔ : W.Δ ∈ maximalIdeal A) (hu : IsUnit W.c₄)

include hΔ hu

/-- The actual nodal smooth reduction kills every residue-prime torsion point of E₀. -/
theorem nodal_smoothReduction_prime_eq_zero (P : ellipticE0 A W) (hP : p • P = 0) :
    smoothReductionHom A W P = 0 := by
  apply nodalProjectivePoint_char_torsion_eq_zero (W.map (residue A)) p
  · rw [map_Δ]
    exact (residue_eq_zero_iff _).mpr hΔ
  · rw [map_c₄]
    exact (hu.map (residue A)).ne_zero
  · rw [← map_nsmul, hP, map_zero]

/-- All p-torsion in the nodal smooth-reduction subgroup lies in the actual infinity fiber. -/
theorem nodal_prime_torsion_mem_ellipticE1 (P : ellipticE0 A W) (hP : p • P = 0) :
    P.val ∈ ellipticE1 A W :=
  (mem_smoothReductionHom_ker_iff A W P).mp
    (nodal_smoothReduction_prime_eq_zero A W p hΔ hu P hP)

variable (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)
  (hc : Nat.card H = p)

include hc

/-- Smooth containment of a prime subgroup strengthens to containment in the formal kernel. -/
theorem primeSubgroup_le_ellipticE1_of_nodal_smooth (hH : H ≤ ellipticE0 A W) :
    H ≤ ellipticE1 A W := by
  intro P hP
  apply nodal_prime_torsion_mem_ellipticE1 A W p hΔ hu ⟨P, hH hP⟩
  have hk : Nat.card H • (⟨P, hP⟩ : H) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard _)
  apply Subtype.ext
  change p • P = 0
  have h := congrArg H.subtype hk
  simpa only [map_nsmul, map_zero, AddSubgroup.subtype_apply, hc] using h

variable [IsDiscreteValuationRing A] [(W.map (algebraMap A K)).IsElliptic]

/-- The exact bad-reduction alternative separates the formal kernel from split components. -/
theorem primeSubgroup_nodal_kernel_or_components (hp2 : 2 < p) :
    H ≤ ellipticE1 A W ∨ (W.nodePoly.map (residue A)).Splits ∧
      Function.Injective (ellipticSubgroupComponentHom A W H) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧
        W.Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n := by
  classical
  by_cases hH : H ≤ ellipticE0 A W
  · exact Or.inl (primeSubgroup_le_ellipticE1_of_nodal_smooth A W p hΔ hu H hc hH)
  · right
    have hs : (W.nodePoly.map (residue A)).Splits := by
      by_contra hns
      exact hH (primeSubgroup_le_ellipticE0_nonsplitNodal A W H p hc hΔ hu hns hp2)
    exact ⟨hs, (primeSubgroup_smooth_or_component_injective A W H p hc).resolve_left hH,
      primeSubgroup_splitNode_depth_dvd A W H p hc hΔ hu hs hH⟩

end FLT.Mazur
