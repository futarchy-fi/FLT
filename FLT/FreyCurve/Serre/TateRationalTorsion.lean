/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.TateTorsion
public import FLT.FreyCurve.Serre.RootsOfUnityInertia
public import FLT.EllipticCurve.SmallResidueTorsion

/-!
# Rational Tate torsion over small residue fields

Large prime roots of unity are trivial in a valued field with small finite
residue field. Consequently the Tate torsion exponent is injective on points
over that field. Identifying this exponent with a Néron component map is not
asserted here.
-/

@[expose] public section

/-- A prime larger than the residue field cannot occur as the order of a
nontrivial root of unity in the valued field. -/
theorem ValuationSubring.eq_one_of_prime_pow_eq_one_of_residue_card_lt
    {K : Type*} [Field K] (A : ValuationSubring K)
    [Finite (IsLocalRing.ResidueField A)] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (IsLocalRing.ResidueField A) < p)
    {x : K} (hx : x ^ p = 1) : x = 1 := by
  have hxmem : x ∈ A := by
    apply A.mem_of_valuation_le_one
    apply (pow_le_one_iff hp.ne_zero).mp
    rw [← map_pow, hx, map_one]
  let y : A := ⟨x, hxmem⟩
  have hy : y ^ p = 1 := Subtype.ext hx
  have hr : IsLocalRing.residue A y = 1 := by
    have hd : orderOf (IsLocalRing.residue A y) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hy, map_one])
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact orderOf_eq_one_iff.mp h
    · have hb := orderOf_le_card (x := IsLocalRing.residue A y)
      omega
  have he := IsLocalRing.eq_of_pow_eq_one_of_residue_eq
    (WeierstrassCurve.isUnit_prime_of_residue_card_lt A hp hcard)
    hy (one_pow p) (hr.trans (map_one _).symm)
  exact congrArg Subtype.val he

open scoped WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

variable {k : Type*} [Field k] [DecidableEq k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (E : WeierstrassCurve k) [E.IsElliptic]
  [E.HasSplitMultiplicativeReduction 𝒪[k]]
  (A : ValuationSubring k) [Finite (IsLocalRing.ResidueField A)]
  {p : ℕ} (hp : p.Prime) (hcard : Nat.card (IsLocalRing.ResidueField A) < p)

include A hp hcard in
/-- A rational Tate torsion point with zero exponent is zero when the residue
field is smaller than the prime order. -/
theorem eq_zero_of_tateTorsionQuotient_eq_zero
    (P : AddSubgroup.torsionBy (E⁄k).Point (p : ℤ))
    (hP : E.tateTorsionQuotient k p P = 0) : P = 0 := by
  obtain ⟨u, m, hu, hm⟩ := E.exists_tatePoint_torsionBy_rep k p P
  have hm0 : (m : ZMod p) = 0 := by
    rw [← E.tateTorsionExponent_eq k P u m hu hm]
    exact hP
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp hm0
  have hroot : (u / E.qUnitSepClosure k ^ c) ^ p = 1 := by
    rw [div_pow, hm, hc, mul_comm (p : ℤ) c, zpow_mul, zpow_natCast]
    simp
  have he : u / E.qUnitSepClosure k ^ c = 1 := by
    apply Units.ext
    exact A.eq_one_of_prime_pow_eq_one_of_residue_card_lt hp hcard
      (congrArg Units.val hroot)
  have huq : u = E.qUnitSepClosure k ^ c := div_eq_one.mp he
  apply Subtype.ext
  change (P : (E⁄k).Point) = 0
  rw [← hu]
  apply (E.tatePoint_eq_zero_iff k u).mpr
  exact Subgroup.mem_zpowers_iff.mpr ⟨c, huq.symm⟩

include A hp hcard in
/-- The Tate exponent embeds rational prime torsion into the cyclic group of
order p; this is not yet an identification with Néron components. -/
theorem tateTorsionQuotient_injective_of_residue_card_lt :
    Function.Injective (E.tateTorsionQuotient k p) := by
  intro P Q h
  apply sub_eq_zero.mp
  apply E.eq_zero_of_tateTorsionQuotient_eq_zero A hp hcard
  rw [map_sub, h, sub_self]


include A hp hcard in
/-- Rational p-torsion has at most p elements under split multiplicative
uniformization over a field with smaller finite residue field. -/
theorem card_tate_torsion_le_prime_of_residue_card_lt :
    Nat.card (AddSubgroup.torsionBy (E⁄k).Point (p : ℤ)) ≤ p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  simpa using Nat.card_le_card_of_injective (E.tateTorsionQuotient k p)
    (E.tateTorsionQuotient_injective_of_residue_card_lt A hp hcard)

end WeierstrassCurve
