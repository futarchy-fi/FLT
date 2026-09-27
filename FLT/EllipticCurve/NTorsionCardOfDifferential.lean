/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.DivisionPolynomialSeparable
public import FLT.EllipticCurve.NTorsionCardOfSeparable
public import FLT.EllipticCurve.TwoTorsionCard

/-!
# Counting torsion from the division-polynomial differential identity

At even indices, the two-torsion points contribute four points, and each
root of `preΨ` contributes two more. The corrected differential identity
supplies both separability and disjointness from the two-torsion roots.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {k : Type*} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]

omit [E.IsElliptic] in
/-- Coprimality with the two-division polynomial separates a division-polynomial
root from all two-torsion x-coordinates. -/
theorem eval_Ψ₂Sq_ne_zero_of_isCoprime_preΨ {n : ℕ}
    (hc : IsCoprime (E.preΨ n) E.Ψ₂Sq) {x : k} (hx : (E.preΨ n).IsRoot x) :
    E.Ψ₂Sq.eval x ≠ 0 := by
  have h := Polynomial.aeval_ne_zero_of_isCoprime hc x
  have hx' : (E.preΨ n).eval x = 0 := hx
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, hx', ne_self_iff_false,
    false_or] using h

omit [E.IsElliptic] in
/-- Away from two-torsion, `preΨ` detects torsion also at even indices. -/
theorem isRoot_preΨ_iff_nsmul_eq_zero_of_not_two [DecidableEq k] {n : ℕ}
    (hn : Even n) {x y : k} (h : E.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • Affine.Point.some x y h ≠ 0) :
    (E.preΨ n).IsRoot x ↔ n • Affine.Point.some x y h = 0 := by
  have he : Even (n : ℤ) := by simpa using hn
  have hz : E.Ψ₂Sq.eval x ≠ 0 := by
    intro hz
    apply h2
    apply (E.isRoot_ΨSq_iff_nsmul_eq_zero h 2).mp
    simpa only [Nat.cast_ofNat, ΨSq_two, Polynomial.IsRoot] using hz
  rw [← E.isRoot_ΨSq_iff_nsmul_eq_zero h n]
  simp only [ΨSq, ite_eq_left he, Polynomial.IsRoot, eval_mul, eval_pow,
    mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), hz, or_false]

/-- Even torsion outside two-torsion is parametrized by the roots of `preΨ`
and the two y-coordinates over each root. -/
noncomputable def evenTorsionOutsideTwoEquivRootFibers [DecidableEq k] {n : ℕ}
    (hn : Even n) (hp : E.preΨ n ≠ 0) (hc : IsCoprime (E.preΨ n) E.Ψ₂Sq) :
    {P : E.toAffine.Point // n • P = 0 ∧ (2 : ℕ) • P ≠ 0} ≃
      (x : (E.preΨ n).rootSet k) × {y : k // E.toAffine.Equation x.val y} where
  toFun P := by
    obtain ⟨P, ht, hz⟩ := P
    cases P with
    | zero => exact (hz (smul_zero (2 : ℕ))).elim
    | some x y h =>
      refine ⟨⟨x, (Polynomial.mem_rootSet_of_ne hp).mpr ?_⟩, ⟨y, h.1⟩⟩
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, Polynomial.IsRoot] using
        (E.isRoot_preΨ_iff_nsmul_eq_zero_of_not_two hn h hz).mpr ht
  invFun P := by
    have h := E.toAffine.equation_iff_nonsingular.mp P.2.property
    have hx : (E.preΨ n).IsRoot P.1.val := by
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, Polynomial.IsRoot] using
        (Polynomial.mem_rootSet_of_ne hp).mp P.1.property
    have hz := E.eval_Ψ₂Sq_ne_zero_of_isCoprime_preΨ hc hx
    have h2 : (2 : ℕ) • Affine.Point.some P.1.val P.2.val h ≠ 0 := by
      intro hzero
      apply hz
      simpa only [Nat.cast_ofNat, ΨSq_two, Polynomial.IsRoot] using
        (E.isRoot_ΨSq_iff_nsmul_eq_zero h 2).mpr hzero
    exact ⟨Affine.Point.some P.1.val P.2.val h,
      (E.isRoot_preΨ_iff_nsmul_eq_zero_of_not_two hn h h2).mp hx, h2⟩
  left_inv P := by
    obtain ⟨P, ht, hz⟩ := P
    cases P with
    | zero => exact (hz (smul_zero (2 : ℕ))).elim
    | some x y h => rfl
  right_inv P := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := P
    rfl

/-- The torsion points outside two-torsion contribute twice the number of
roots of an even division polynomial coprime to the two-division polynomial. -/
theorem card_even_torsion_outside_two [DecidableEq k] [IsSepClosed k] {n : ℕ}
    (hn : Even n) (hp : E.preΨ n ≠ 0) (hc : IsCoprime (E.preΨ n) E.Ψ₂Sq) :
    Nat.card {P : E.toAffine.Point // n • P = 0 ∧ (2 : ℕ) • P ≠ 0} =
      2 * Nat.card ((E.preΨ n).rootSet k) := by
  classical
  have hcard (x : (E.preΨ n).rootSet k) :
      Nat.card {y : k // E.toAffine.Equation x.val y} = 2 := by
    apply E.card_equation_of_Ψ₂Sq_ne_zero
    apply E.eval_Ψ₂Sq_ne_zero_of_isCoprime_preΨ hc
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, Polynomial.IsRoot] using
      (Polynomial.mem_rootSet_of_ne hp).mp x.property
  let (x : (E.preΨ n).rootSet k) : Finite {y : k // E.toAffine.Equation x.val y} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  rw [Nat.card_congr (E.evenTorsionOutsideTwoEquivRootFibers hn hp hc), Nat.card_sigma]
  simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

/-- Even torsion splits into two-torsion and the two points over each root of
`preΨ`, provided these roots are disjoint from the two-torsion x-coordinates. -/
theorem card_even_torsion_eq_roots [DecidableEq k] [IsSepClosed k] {n : ℕ}
    (hn : Even n) (h2 : (2 : k) ≠ 0) (hp : E.preΨ n ≠ 0)
    (hc : IsCoprime (E.preΨ n) E.Ψ₂Sq) :
    Nat.card {P : E.toAffine.Point // n • P = 0} =
      4 + 2 * Nat.card ((E.preΨ n).rootSet k) := by
  classical
  let T := {P : E.toAffine.Point // n • P = 0}
  let e2 : {P : T // (2 : ℕ) • P.val = 0} ≃ {P : E.toAffine.Point // (2 : ℕ) • P = 0} :=
    { toFun := fun P => ⟨P.val.val, P.property⟩
      invFun := fun P => ⟨⟨P.val, by
        obtain ⟨m, hm⟩ := hn
        rw [hm, ← two_mul, mul_smul, smul_comm (2 : ℕ) m, P.property, smul_zero]⟩, P.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eRest : {P : T // ¬(2 : ℕ) • P.val = 0} ≃
      {P : E.toAffine.Point // n • P = 0 ∧ (2 : ℕ) • P ≠ 0} :=
    { toFun := fun P => ⟨P.val.val, P.val.property, P.property⟩
      invFun := fun P => ⟨⟨P.val, P.property.1⟩, P.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard2 : Nat.card {P : T // (2 : ℕ) • P.val = 0} = 4 := by
    rw [Nat.card_congr e2, E.card_two_torsion h2]
  have hcardRest := E.card_even_torsion_outside_two hn hp hc
  have hn0 : n ≠ 0 := by rintro rfl; simp at hp
  let : Finite T := (E.finite_setOf_nsmul_eq_zero (Nat.pos_of_ne_zero hn0)).to_subtype
  change Nat.card T = _
  rw [← Nat.card_congr (Equiv.sumCompl (fun P : T => (2 : ℕ) • P.val = 0)), Nat.card_sum,
    hcard2, Nat.card_congr eRest, hcardRest]

/-- Separability and disjointness from two-torsion give the expected cardinality
at even indices nonzero in a separably closed field. -/
theorem card_even_torsion_of_separable [DecidableEq k] [IsSepClosed k] {n : ℕ}
    (hn : Even n) (hchar : (n : k) ≠ 0) (hsep : (E.preΨ n).Separable)
    (hc : IsCoprime (E.preΨ n) E.Ψ₂Sq) :
    Nat.card {P : E.toAffine.Point // n • P = 0} = n ^ 2 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hchar
  have h2 : (2 : k) ≠ 0 := by
    obtain ⟨m, hm⟩ := hn
    intro h
    apply hchar
    rw [hm, Nat.cast_add, ← two_mul, h, zero_mul]
  rw [E.card_even_torsion_eq_roots hn h2 hsep.ne_zero hc, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree hsep (by
      simpa using IsSepClosed.splits_of_separable _ hsep)]
  have hcast : ((n : ℤ) : k) ≠ 0 := by exact_mod_cast hchar
  have he : Even (n : ℤ) := by simpa using hn
  rw [E.natDegree_preΨ hcast, ite_eq_left he, Int.natAbs_natCast]
  have hn2 : 2 ≤ n := by obtain ⟨m, hm⟩ := hn; omega
  have hs : n ^ 2 % 2 = 0 := by simp [Nat.pow_mod, Nat.even_iff.mp hn]
  have hn4 : 4 ≤ n ^ 2 := by nlinarith
  omega

/-- The corrected differential identity suffices for the torsion cardinality
at every index nonzero in a separably closed field. -/
theorem card_torsion_of_divisionDifferentialDefect [DecidableEq k] [IsSepClosed k] {n : ℕ}
    (hchar : (n : k) ≠ 0) (hd : E.divisionDifferentialDefect n = 0) :
    Nat.card {P : E.toAffine.Point // n • P = 0} = n ^ 2 := by
  have hs := E.separable_preΨ_of_divisionDifferentialDefect hchar hd
  rcases Nat.even_or_odd n with hn | hn
  · exact E.card_even_torsion_of_separable hn hchar hs
      (E.isCoprime_preΨ_Ψ₂Sq_of_divisionDifferentialDefect hn hchar hd)
  · exact E.card_odd_torsion_of_separable hn hchar hs

end WeierstrassCurve
