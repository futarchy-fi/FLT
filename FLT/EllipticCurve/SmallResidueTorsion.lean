/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointReductionKernel
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Large prime torsion over small residue fields

The elementary coordinate bound suffices over fields of two or three elements.
Consequently large prime torsion on a good integral model reduces to zero.
The division polynomial, normalized by its unit leading coefficient, also
excludes prime-to-residue-characteristic torsion in the reduction kernel.
These results do not address bad reduction or prove rational torsion exclusion.
-/

@[expose] public section

namespace WeierstrassCurve

/-- Count nonsingular affine points by their two coordinates, plus infinity. -/
theorem card_point_le_coordinates {F : Type*} [Field F] [Finite F]
    (E : WeierstrassCurve F) :
    Nat.card E.toAffine.Point ≤ Nat.card F ^ 2 + 1 := by
  rw [Nat.card_congr E.toAffine.nonsingularPointEquiv]
  change Nat.card (Option {xy : F × F // E.toAffine.Nonsingular xy.1 xy.2}) ≤ _
  rw [Finite.card_option]
  have h := Nat.card_le_card_of_injective
    (Subtype.val : {xy : F × F // E.toAffine.Nonsingular xy.1 xy.2} → F × F)
    Subtype.val_injective
  simpa only [Nat.card_prod, pow_two] using Nat.add_le_add_right h 1

/-- Over a finite field, a prime larger than the coordinate bound kills only zero. -/
theorem eq_zero_of_prime_nsmul_of_card_lt {F : Type*} [Field F] [DecidableEq F] [Finite F]
    (E : WeierstrassCurve F) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F ^ 2 + 1 < p) (P : E.toAffine.Point)
    (hP : p • P = 0) : P = 0 := by
  let : Finite E.toAffine.Point :=
    Finite.of_equiv (Option {xy : F × F // E.toAffine.Nonsingular xy.1 xy.2})
      E.toAffine.nonsingularPointEquiv.symm
  have hd := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hP
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact AddMonoid.addOrderOf_eq_one_iff.mp h
  · have hb := (addOrderOf_le_card (x := P)).trans (E.card_point_le_coordinates)
    omega

/-- For residue fields of size at most three, every point killed by a prime at
least seventeen lies in the reduction kernel. No algebraic closure is assumed. -/
theorem reducePoint_eq_zero_of_large_prime
    {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K) (W : WeierstrassCurve A)
    [(W.map (IsLocalRing.residue A)).IsElliptic]
    [Finite (IsLocalRing.ResidueField A)]
    (hcard : Nat.card (IsLocalRing.ResidueField A) ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p)
    {P : (W.map (algebraMap A K)).toAffine.Point} (hP : p • P = 0) :
    W.reducePoint A P = 0 := by
  classical
  apply (W.map (IsLocalRing.residue A)).eq_zero_of_prime_nsmul_of_card_lt hp
      (P := W.reducePoint A P)
  · have hb := Nat.pow_le_pow_left hcard 2
    norm_num at hb
    omega
  · exact W.nsmul_reducePoint_eq_zero A p hP

/-- Torsion of order invertible in the valuation ring cannot reduce to infinity,
unless the point itself is infinity. -/
theorem eq_zero_of_reducePoint_eq_zero_of_unit_nsmul
    {K : Type*} [Field K] [DecidableEq K]
    (A : ValuationSubring K) (W : WeierstrassCurve A)
    [(W.map (IsLocalRing.residue A)).IsElliptic]
    {n : ℕ} (hn : IsUnit (n : A))
    {P : (W.map (algebraMap A K)).toAffine.Point}
    (ht : n • P = 0) (hr : W.reducePoint A P = 0) : P = 0 := by
  classical
  cases P with
  | zero => rfl
  | some x y h =>
    have hl : IsUnit (W.ΨSq (n : ℤ)).leadingCoeff := by
      rw [W.leadingCoeff_ΨSq (by simpa using hn.ne_zero)]
      simpa using hn.pow 2
    have hxroot := (W.map (algebraMap A K)).isRoot_ΨSq_of_nsmul_eq_zero h n ht
    have hxint : IsIntegral A x := by
      refine ⟨hl.unit⁻¹ • W.ΨSq (n : ℤ),
        Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hl, ?_⟩
      have he : (W.ΨSq (n : ℤ)).eval₂ (algebraMap A K) x = 0 := by
        simpa only [map_ΨSq, Polynomial.IsRoot, Polynomial.eval_map] using hxroot
      simp only [Units.smul_def, Polynomial.eval₂_smul, he, mul_zero]
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxint
    have hx : x ∈ A := ha ▸ a.property
    have hy : y ∈ A := W.mem_y_of_mem_x A h.1 hx
    simp only [reducePoint, hx, hy, and_self, dite_eq_left] at hr
    cases hr

/-- A good model with at most three residue elements has no nonzero point killed
by a prime at least seventeen. -/
theorem eq_zero_of_large_prime_small_residue
    {K : Type*} [Field K] [DecidableEq K]
    (A : ValuationSubring K) (W : WeierstrassCurve A)
    [(W.map (IsLocalRing.residue A)).IsElliptic]
    [Finite (IsLocalRing.ResidueField A)]
    (hcard : Nat.card (IsLocalRing.ResidueField A) ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p)
    {P : (W.map (algebraMap A K)).toAffine.Point} (hP : p • P = 0) :
    P = 0 := by
  classical
  have hu : IsUnit (p : A) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_natCast]
    intro hz
    have hd : addOrderOf (1 : IsLocalRing.ResidueField A) ∣ p :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa using hz)
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact one_ne_zero (AddMonoid.addOrderOf_eq_one_iff.mp h)
    · have hb := addOrderOf_le_card (x := (1 : IsLocalRing.ResidueField A))
      omega
  exact W.eq_zero_of_reducePoint_eq_zero_of_unit_nsmul A hu hP
    (W.reducePoint_eq_zero_of_large_prime A hcard hp hp17 hP)

/-- Good reduction over a residue field of size at most three excludes points
of large prime order on the generic fiber. -/
theorem no_large_prime_torsion_of_small_residue
    {K : Type*} [Field K] [DecidableEq K]
    (A : ValuationSubring K) (W : WeierstrassCurve A)
    [(W.map (IsLocalRing.residue A)).IsElliptic]
    [Finite (IsLocalRing.ResidueField A)]
    (hcard : Nat.card (IsLocalRing.ResidueField A) ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p) :
    ¬ ∃ P : (W.map (algebraMap A K)).toAffine.Point, addOrderOf P = p := by
  rintro ⟨P, hP⟩
  have ht : p • P = 0 := hP ▸ addOrderOf_nsmul_eq_zero P
  have hz := W.eq_zero_of_large_prime_small_residue A hcard hp hp17 ht
  simp only [hz, addOrderOf_zero] at hP
  omega

end WeierstrassCurve
