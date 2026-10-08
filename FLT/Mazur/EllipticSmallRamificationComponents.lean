/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodalPrimeReductionKernel
public import FLT.Mazur.EllipticSmallRamificationTorsion

/-!
# Injective split-component reduction under small ramification

A prime-order subgroup cannot lie in the actual formal kernel. In nodal
reduction this eliminates the kernel branch, so the node splits and the
original subgroup injects into the component group.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A]
  (p : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0)
  (he : RaynaudParameters.order (p : A) < p - 1)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (hc : Nat.card H = p)

include hp0 he hc

/-- Small absolute ramification excludes a prime-order subgroup in E₁. -/
theorem primeSubgroup_not_le_ellipticE1_small_ramification : ¬ H ≤ ellipticE1 A W := by
  intro hH
  have hz (P : H) : P = 0 := by
    have hn : p • P = 0 := by
      rw [← hc]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)
    let Q : ellipticE1 A W := ⟨P.val, hH P.property⟩
    have hq : p • Q = 0 := by
      apply Subtype.ext
      exact congrArg H.subtype hn
    have hq0 := (ellipticE1_prime_nsmul_eq_zero_iff_small_ramification A W p hp0 he Q).mp hq
    apply Subtype.ext
    exact congrArg (ellipticE1 A W).subtype hq0
  let _ : Subsingleton H := ⟨fun x y => (hz x).trans (hz y).symm⟩
  have hc1 : Nat.card H = 1 := Nat.card_unique
  have hp := (Fact.out : p.Prime).one_lt
  omega

variable [Finite (ResidueField A)] [CharP (ResidueField A) p]
  [(W.map (algebraMap A K)).IsElliptic]

/-- The nodal component comparison is injective, and p divides the positive depth. -/
theorem primeSubgroup_split_components_small_ramification
    (hΔ : W.Δ ∈ maximalIdeal A) (hu : IsUnit W.c₄) (hp2 : 2 < p) :
    (W.nodePoly.map (residue A)).Splits ∧
      Function.Injective (ellipticSubgroupComponentHom A W H) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧
        W.Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n := by
  exact (primeSubgroup_nodal_kernel_or_components A W p hΔ hu H hc hp2).resolve_left
    (primeSubgroup_not_le_ellipticE1_small_ramification A W p hp0 he H hc)

end FLT.Mazur
