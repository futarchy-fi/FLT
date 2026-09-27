/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.DivisionPolynomialDifferentialIdentity
public import FLT.EllipticCurve.NTorsionCardOfDifferential
public import FLT.EllipticCurve.PointDivisor
public import Mathlib.GroupTheory.Index

/-!
# Multiplication fibers of torsion points

Counting the kernel proves that multiplication by n maps n²-torsion onto
n-torsion. A fiber is a translate of the n-torsion subgroup. The quotient
of its point-ideal product by that of the zero fiber is principal.
-/

@[expose] public section

open scoped nonZeroDivisors
namespace WeierstrassCurve.Affine.Point
variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
/-- The subgroup of points killed by n. -/
abbrev torsionKernel (n : ℕ) : AddSubgroup W.Point :=
  (nsmulAddMonoidHom (α := W.Point) n).ker
/-- The kernel of a positive multiplication map is finite. -/
theorem finite_torsionKernel {n : ℕ} (hn : n ≠ 0) : Finite (torsionKernel W n) := by
  exact (W.finite_setOf_nsmul_eq_zero (Nat.pos_of_ne_zero hn)).to_subtype
/-- The kernel has n² points over a separably closed field when n is invertible. -/
theorem card_torsionKernel [IsSepClosed F] {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (torsionKernel W n) = n ^ 2 := by
  exact W.card_torsion_of_divisionDifferentialDefect hn (W.divisionDifferentialDefect_eq_zero n)
/-- Multiplication by n from n²-torsion to n-torsion. -/
def torsionMul (n : ℕ) : torsionKernel W (n * n) →+ torsionKernel W n where
  toFun P := ⟨n • P.val, by
    change n • (n • P.val) = 0
    rw [← mul_smul]
    exact P.property⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' P Q := Subtype.ext (smul_add _ _ _)
/-- The kernel of multiplication on n²-torsion is precisely n-torsion. -/
def torsionMulKerEquiv (n : ℕ) : (torsionMul W n).ker ≃ torsionKernel W n where
  toFun P := ⟨P.val.val, by
    have h := congrArg Subtype.val P.property
    exact h⟩
  invFun P := ⟨⟨P.val, by
    change (n * n) • P.val = 0
    rw [mul_smul, show n • P.val = 0 from P.property, smul_zero]⟩,
      Subtype.ext P.property⟩
  left_inv P := rfl
  right_inv P := rfl
/-- Every n-torsion point has an n-division point over a separably closed field. -/
theorem exists_nsmul_eq_of_torsion [IsSepClosed F] {n : ℕ} (hn : (n : F) ≠ 0)
    (T : W.Point) (hT : n • T = 0) : ∃ Q : W.Point, n • Q = T := by
  have hn0 : n ≠ 0 := by intro hz; simp [hz] at hn
  have := finite_torsionKernel W hn0
  have := finite_torsionKernel W (mul_ne_zero hn0 hn0)
  have hs : Function.Surjective (torsionMul W n) := by
    apply AddMonoidHom.surjective_of_card_ker_le_div
    rw [Nat.card_congr (torsionMulKerEquiv W n), card_torsionKernel W hn,
      card_torsionKernel W (show ((n * n : ℕ) : F) ≠ 0 by simpa using mul_ne_zero hn hn),
      mul_pow, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (pow_ne_zero 2 hn0))]
  obtain ⟨Q, hQ⟩ := hs ⟨T, hT⟩
  exact ⟨Q.val, congrArg Subtype.val hQ⟩

omit [W.IsElliptic] in
/-- Translating the kernel by Q parametrizes the entire fiber above nQ. -/
def torsionFiberEquiv (n : ℕ) (Q : W.Point) :
    torsionKernel W n ≃ {P : W.Point // n • P = n • Q} where
  toFun R := ⟨R.val + Q, by rw [nsmul_add, show n • R.val = 0 from R.property, zero_add]⟩
  invFun P := ⟨P.val - Q, by
    change n • (P.val - Q) = 0
    rw [nsmul_sub, P.property, sub_self]⟩
  left_inv R := Subtype.ext (add_sub_cancel_right _ _)
  right_inv P := Subtype.ext (sub_add_cancel _ _)

/-- A nonempty fiber of multiplication by n has n² points when n is invertible. -/
theorem card_torsionFiber [IsSepClosed F] {n : ℕ} (hn : (n : F) ≠ 0) (Q : W.Point) :
    Nat.card {P : W.Point // n • P = n • Q} = n ^ 2 := by
  rw [← Nat.card_congr (torsionFiberEquiv W n Q), card_torsionKernel W hn]

/-- The finite set of all n-torsion points. -/
noncomputable def torsionPoints (n : ℕ) (hn : n ≠ 0) : Finset W.Point :=
  (W.finite_setOf_nsmul_eq_zero (Nat.pos_of_ne_zero hn)).toFinset

/-- Membership in the torsion point set is the multiplication equation. -/
@[simp] theorem mem_torsionPoints (n : ℕ) (hn : n ≠ 0) (P : W.Point) :
    P ∈ torsionPoints W n hn ↔ n • P = 0 := Set.Finite.mem_toFinset _

/-- The finite torsion point set has n² elements when n is invertible. -/
theorem card_torsionPoints [IsSepClosed F] {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) :
    (torsionPoints W n hn).card = n ^ 2 := by
  rw [torsionPoints, ← Set.ncard_eq_toFinset_card _
    (W.finite_setOf_nsmul_eq_zero (Nat.pos_of_ne_zero hn)), ← Nat.card_coe_set_eq]
  exact card_torsionKernel W hchar

/-- The affine fractional ideal of the difference between the fiber above nQ
and the fiber above the origin. -/
noncomputable def fiberIdeal (n : ℕ) (hn : n ≠ 0) (Q : W.Point) :
    (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  (∏ R ∈ torsionPoints W n hn, fractionalIdeal (R + Q)) /
    (∏ R ∈ torsionPoints W n hn, fractionalIdeal R)

/-- The point sum of the difference between the two fibers is n²Q. -/
theorem sum_torsionPoints_translate_sub [IsSepClosed F] {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) (Q : W.Point) :
    (∑ R ∈ torsionPoints W n hn, (R + Q)) -
      (∑ R ∈ torsionPoints W n hn, R) = (n ^ 2) • Q := by
  rw [Finset.sum_add_distrib, Finset.sum_const, card_torsionPoints W hn hchar,
    add_sub_cancel_left]

/-- If nQ is n-torsion, the difference of multiplication fibers has a nonzero
rational generator on the affine chart. -/
theorem exists_generator_fiberIdeal [IsSepClosed F] {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) (Q : W.Point) (hQ : n • (n • Q) = 0) :
    ∃ g : W.FunctionField, g ≠ 0 ∧
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ g = fiberIdeal W n hn Q := by
  apply (exists_generator_div_prod_iff _ _ _ _).mpr
  apply sub_eq_zero.mp
  rw [sum_torsionPoints_translate_sub W hn hchar, pow_two, mul_smul, hQ]

end WeierstrassCurve.Affine.Point
