/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitDepthModel
public import FLT.Mazur.EllipticNodeComponentCyclic
public import FLT.Mazur.EllipticComponentVariableChange
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Split nodal components without a supplied depth model

A nonzero discriminant in a separated local ring has a finite positive
ideal-adic depth. Existing integral normalization then constructs the
split depth model, and its cyclic component quotient transports to the
original equation. Its order divides the discriminant depth.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A nonzero element of the maximal ideal has a finite positive exact depth. -/
theorem exists_positive_maximalIdeal_depth {R : Type*} [CommRing R] [IsLocalRing R]
    [IsHausdorff (maximalIdeal R) R] {x : R} (hx0 : x ≠ 0) (hx : x ∈ maximalIdeal R) :
    ∃ n : ℕ, 0 < n ∧ x ∈ maximalIdeal R ^ n ∧ x ∉ maximalIdeal R ^ (n + 1) := by
  classical
  have he : ∃ n : ℕ, x ∉ maximalIdeal R ^ (n + 1) := by
    by_contra hn
    push Not at hn
    apply hx0
    apply IsHausdorff.haus' (I := maximalIdeal R)
    intro n
    simpa only [SModEq.zero, smul_eq_mul, ← Ideal.one_eq_top, mul_one] using
      (Ideal.pow_le_pow_right (by omega : n ≤ n + 1) (hn n))
  let n := Nat.find he
  have hnot : x ∉ maximalIdeal R ^ (n + 1) := Nat.find_spec he
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := by omega
    exact hnot (by simpa only [hn0, zero_add, pow_one] using hx)
  refine ⟨n, hn, ?_, hnot⟩
  have hm := of_not_not (Nat.find_min he (show n - 1 < Nat.find he from by omega))
  simpa only [Nat.sub_add_cancel (show 1 ≤ n from hn)] using hm

/-- A split node admits an actual depth model at a finite positive discriminant depth. -/
theorem exists_splitNodeDepth_model {K : Type*} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : IsUnit W.c₄)
    (hsplit : (W.nodePoly.map (residue A)).Splits) :
    ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧ W.Δ ∉ maximalIdeal A ^ (n + 1) ∧
      ∃ π r s t : A, SplitNodeDepth ((VariableChange.mk 1 r s t : VariableChange A) • W) π n := by
  have hΔ0 : W.Δ ≠ 0 := by
    intro hz
    apply (W.map (algebraMap A K)).isUnit_Δ.ne_zero
    simp [map_Δ, hz]
  obtain ⟨n, hn, hd, hd'⟩ := exists_positive_maximalIdeal_depth hΔ0 hΔ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨r, s, t, h1, h2, h3, h4, h6, h6'⟩ :=
    exists_split_node_discriminant_depth W n hn hd hd' hc hsplit
  exact ⟨n, hn, hd, hd', π, r, s, t,
    ⟨hn, hπ.ne_zero, hπ.maximalIdeal_eq, h1, h2, h3, h4, h6, h6'⟩⟩

/-- The split nodal component quotient is finite cyclic, of order dividing discriminant depth. -/
theorem splitNode_components {K : Type*} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : IsUnit W.c₄)
    (hsplit : (W.nodePoly.map (residue A)).Splits) :
    Finite (EllipticComponentQuotient A W) ∧ IsAddCyclic (EllipticComponentQuotient A W) ∧
      ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧ W.Δ ∉ maximalIdeal A ^ (n + 1) ∧
        Nat.card (EllipticComponentQuotient A W) ∣ n := by
  classical
  obtain ⟨n, hn, hd, hd', π, r, s, t, D⟩ := exists_splitNodeDepth_model A W hΔ hc hsplit
  let C : VariableChange A := .mk 1 r s t
  let e := integralComponentVariableChange A W C
  let := finite_ellipticComponentQuotient_of_splitNodeDepth D
  let := isAddCyclic_ellipticComponentQuotient_of_splitNodeDepth D
  refine ⟨Finite.of_equiv _ e.toEquiv, ?_, n, hn, hd, hd', ?_⟩
  · exact isAddCyclic_of_surjective e e.surjective
  · rw [← Nat.card_congr e.toEquiv]
    exact natCard_ellipticComponentQuotient_dvd_splitNodeDepth D

end FLT.Mazur
