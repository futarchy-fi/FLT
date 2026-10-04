/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.TateRationalTorsion

/-!
# Valuation classes of Tate points

Valuation descends from multiplicative representatives modulo powers of q to
a homomorphism on Tate points. This is an algebraic valuation quotient;
identification with geometric Néron components is not asserted.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

variable {k : Type*} [Field k] [DecidableEq k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (E : WeierstrassCurve k) [E.IsElliptic]
  [E.HasSplitMultiplicativeReduction 𝒪[k]]

/-- Valuation on nonzero multiplicative representatives. -/
noncomputable def tateUnitValuation : kˣ →* (ValueGroupWithZero k)ˣ :=
  Units.map (valuation k).toMonoidHom

/-- The valuation class of a Tate point, modulo the valuation of its period. -/
noncomputable def tateValuationClass :
    (E⁄k).Point →+ Additive ((ValueGroupWithZero k)ˣ ⧸
      Subgroup.zpowers (tateUnitValuation (k := k) (E.qUnitSepClosure k))) :=
  (QuotientGroup.map (Subgroup.zpowers (E.qUnitSepClosure k))
    (Subgroup.zpowers (tateUnitValuation (k := k) (E.qUnitSepClosure k)))
    (tateUnitValuation (k := k)) (by
      intro u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, (map_zpow _ _ _).symm⟩)).toAdditive.comp
    (E.tateEquivSepClosure k).symm.toAddMonoidHom

/-- Compute the descended valuation class using any Tate representative. -/
theorem tateValuationClass_tatePoint (u : kˣ) :
    E.tateValuationClass (E.tatePoint k u) =
      Additive.ofMul (QuotientGroup.mk (tateUnitValuation (k := k) u)) := by
  simp [tateValuationClass, tatePoint]

/-- Zero valuation class means a representative's valuation is a power of
the valuation of q. -/
theorem tateValuationClass_tatePoint_eq_zero_iff (u : kˣ) :
    E.tateValuationClass (E.tatePoint k u) = 0 ↔
      ∃ c : ℤ, valuation k (u : k) =
        valuation k ((E.qUnitSepClosure k : kˣ) : k) ^ c := by
  rw [tateValuationClass_tatePoint]
  change (QuotientGroup.mk (tateUnitValuation (k := k) u) = 1) ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [tateUnitValuation] using (congrArg Units.val hc).symm
  · rintro ⟨c, hc⟩
    refine ⟨c, Units.ext ?_⟩
    simpa [tateUnitValuation] using hc.symm


/-- The kernel consists exactly of points admitting a representative of
valuation one. This describes the algebraic kernel, not a geometric component. -/
theorem tateValuationClass_eq_zero_iff (P : (E⁄k).Point) :
    E.tateValuationClass P = 0 ↔
      ∃ u : kˣ, valuation k (u : k) = 1 ∧ E.tatePoint k u = P := by
  constructor
  · intro hP
    obtain ⟨z, hz⟩ := (E.tateEquivSepClosure k).surjective P
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective z.toMul
    have hup : E.tatePoint k u = P := by
      change E.tateEquivSepClosure k (Additive.ofMul ↑u) = P
      rw [hu]
      exact hz
    obtain ⟨c, hc⟩ := (E.tateValuationClass_tatePoint_eq_zero_iff u).mp (hup ▸ hP)
    let v := u / E.qUnitSepClosure k ^ c
    refine ⟨v, ?_, ?_⟩
    · change valuation k ((u / E.qUnitSepClosure k ^ c : kˣ) : k) = 1
      simp only [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val,
        map_div₀, map_zpow₀, hc]
      exact div_self (zpow_ne_zero _ ((valuation k).ne_zero_iff.mpr
        (E.qUnitSepClosure k).ne_zero))
    · have hquot : (v : kˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure k)) = u := by
        apply QuotientGroup.eq_iff_div_mem.mpr
        apply Subgroup.mem_zpowers_iff.mpr
        refine ⟨-c, ?_⟩
        dsimp [v]
        simp [zpow_neg, div_eq_mul_inv, mul_comm, mul_left_comm]
      change E.tateEquivSepClosure k (Additive.ofMul ↑v) = P
      rw [hquot]
      exact hup
  · rintro ⟨u, hu, rfl⟩
    apply (E.tateValuationClass_tatePoint_eq_zero_iff u).mpr
    exact ⟨0, by simpa using hu⟩

/-- On torsion, a trivial valuation class forces a trivial Tate exponent. -/
theorem tateTorsionQuotient_eq_zero_of_valuationClass_eq_zero
    {n : ℕ} (P : AddSubgroup.torsionBy (E⁄k).Point (n : ℤ))
    (hP : E.tateValuationClass P = 0) : E.tateTorsionQuotient k n P = 0 := by
  obtain ⟨u, m, hu, hm⟩ := E.exists_tatePoint_torsionBy_rep k n P
  obtain ⟨c, hc⟩ := (E.tateValuationClass_tatePoint_eq_zero_iff u).mp (hu ▸ hP)
  have hq : valuation k ((E.qUnitSepClosure k : kˣ) : k) < 1 := by
    simpa [qUnitSepClosure, qUnit] using E.valuation_q_lt_one
  have he : valuation k ((E.qUnitSepClosure k : kˣ) : k) ^ m =
      valuation k ((E.qUnitSepClosure k : kˣ) : k) ^ (c * n) := by
    have hv := congrArg (fun z : kˣ => valuation k (z : k)) hm
    simpa only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      map_pow, map_zpow₀, hc, zpow_mul, zpow_natCast] using hv.symm
  have hm' : m = c * n := by
    apply (zpow_right_strictAnti₀
      (zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr
        (E.qUnitSepClosure k).ne_zero)) hq).injective
    exact he
  change E.tateTorsionExponent k n P = 0
  rw [E.tateTorsionExponent_eq k P u m hu hm, hm']
  simp

/-- Large prime torsion injects into the valuation quotient of Tate points. -/
theorem tateValuationClass_injective_on_prime_torsion
    (A : ValuationSubring k) [Finite (IsLocalRing.ResidueField A)]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (IsLocalRing.ResidueField A) < p) :
    Function.Injective (fun P : AddSubgroup.torsionBy (E⁄k).Point (p : ℤ) =>
      E.tateValuationClass P) := by
  intro P Q h
  dsimp only at h
  apply sub_eq_zero.mp
  apply E.eq_zero_of_tateTorsionQuotient_eq_zero A hp hcard
  apply E.tateTorsionQuotient_eq_zero_of_valuationClass_eq_zero
  change E.tateValuationClass ((P : (E⁄k).Point) - Q) = 0
  rw [map_sub, h, sub_self]

end WeierstrassCurve
