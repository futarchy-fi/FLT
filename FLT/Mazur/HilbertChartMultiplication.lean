/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartEquations
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Multiplication from a finite table

Coordinate identities turn the explicit Hilbert equations into ring laws.
The proofs work in every commutative coefficient ring, including the zero ring.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace FLT.Mazur.HilbertChart

variable {S : Type*} [CommRing S] {d : ℕ}

/-- Bilinear multiplication on the coordinate module from a finite table. -/
def tableMul (c : Fin d → Fin d → Fin d → S) (a b : Fin d → S) (k : Fin d) : S :=
  ∑ i, ∑ j, a i * b j * c i j k

variable (c : Fin d → Fin d → Fin d → S)

/-- The table product distributes in its first argument. -/
theorem tableMul_add_left (a b z : Fin d → S) :
    tableMul c (a + b) z = tableMul c a z + tableMul c b z := by
  ext k
  simp only [tableMul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The table product distributes in its second argument. -/
theorem tableMul_add_right (a b z : Fin d → S) :
    tableMul c a (b + z) = tableMul c a b + tableMul c a z := by
  ext k
  simp only [tableMul, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- Scalars commute with multiplication in the first argument. -/
theorem tableMul_smul_left (r : S) (a b : Fin d → S) :
    tableMul c (r • a) b = r • tableMul c a b := by
  ext k
  simp only [tableMul, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- A symmetric table gives a commutative product. -/
theorem tableMul_comm (hc : ∀ i j k, c i j k = c j i k) (a b : Fin d → S) :
    tableMul c a b = tableMul c b a := by
  ext k
  rw [tableMul, tableMul, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hc i j k]
  ring

/-- The unit equations give a left identity on all vectors. -/
theorem tableMul_unit_left (b : Fin d → S)
    (hb : ∀ i k, (∑ j, b j * c j i k) = if i = k then 1 else 0)
    (a : Fin d → S) : tableMul c b a = a := by
  ext k
  rw [tableMul, Finset.sum_comm]
  -- Factor the coefficient of the arbitrary vector out of the inner sum.
  have h (i : Fin d) : (∑ j, b j * a i * c j i k) = a i * ∑ j, b j * c j i k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [h, hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- The summed table equations give associativity on arbitrary vectors. -/
theorem tableMul_assoc
    (hc : ∀ i j k l, (∑ m, c i j m * c m k l) = ∑ m, c j k m * c i m l)
    (a b z : Fin d → S) : tableMul c (tableMul c a b) z =
      tableMul c a (tableMul c b z) := by
  ext l
  simp only [tableMul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = a i * b j * z k * ∑ m, c i j m * c m k l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = a i * b j * z k * ∑ m, c j k m * c i m l := by rw [hc]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring

end FLT.Mazur.HilbertChart
