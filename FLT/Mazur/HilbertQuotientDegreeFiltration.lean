/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMonomialFiberBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Degree filtration of an actual polynomial quotient

Once two consecutive degree pieces agree, multiplication by every ambient
coordinate preserves that piece. Polynomial induction then proves that the
piece is the whole quotient. This supplies the stabilization step for uniform
finite polynomial coordinates, without a simultaneous choice of basis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart

variable (K I : Type*) [Field K] (J : Ideal (MvPolynomial I K))

/-- The image of polynomials of total degree at most `n` in the actual quotient. -/
def quotientDegreePiece (n : ℕ) : Submodule K (MvPolynomial I K ⧸ J) :=
  (MvPolynomial.restrictTotalDegree I K n).map (Ideal.Quotient.mkₐ K J).toLinearMap

/-- Membership provides an actual polynomial representative with the stated degree bound. -/
theorem mem_quotientDegreePiece_iff (n : ℕ) (x : MvPolynomial I K ⧸ J) :
    x ∈ quotientDegreePiece K I J n ↔
      ∃ p : MvPolynomial I K, p.totalDegree ≤ n ∧ Ideal.Quotient.mk J p = x := by
  simp only [quotientDegreePiece, Submodule.mem_map, MvPolynomial.mem_restrictTotalDegree,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- Enlarging the allowed total degree enlarges the quotient piece. -/
theorem quotientDegreePiece_mono : Monotone (quotientDegreePiece K I J) := by
  intro n m h x hx
  obtain ⟨p, hp, rfl⟩ := (mem_quotientDegreePiece_iff K I J n x).mp hx
  exact (mem_quotientDegreePiece_iff K I J m _).mpr ⟨p, hp.trans h, rfl⟩

/-- Every constant belongs to every degree piece, including degree zero. -/
theorem quotientDegreePiece_constant (n : ℕ) (a : K) :
    Ideal.Quotient.mk J (MvPolynomial.C a) ∈ quotientDegreePiece K I J n :=
  (mem_quotientDegreePiece_iff K I J n _).mpr
    ⟨MvPolynomial.C a, by simp only [MvPolynomial.totalDegree_C, Nat.zero_le], rfl⟩

/-- Multiplication by one ambient coordinate increases the bound by at most one. -/
theorem quotientDegreePiece_mul_variable (n : ℕ) (i : I)
    (x : MvPolynomial I K ⧸ J) (hx : x ∈ quotientDegreePiece K I J n) :
    x * Ideal.Quotient.mk J (MvPolynomial.X i) ∈ quotientDegreePiece K I J (n + 1) := by
  obtain ⟨p, hp, rfl⟩ := (mem_quotientDegreePiece_iff K I J n x).mp hx
  apply (mem_quotientDegreePiece_iff K I J (n + 1) _).mpr
  refine ⟨p * MvPolynomial.X i, ?_, map_mul _ _ _⟩
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa only [MvPolynomial.totalDegree_X] using Nat.add_le_add_right hp 1)

/-- A stationary degree piece is the whole quotient, even before finite-dimensionality. -/
theorem quotientDegreePiece_eq_top_of_stable (n : ℕ)
    (h : quotientDegreePiece K I J n = quotientDegreePiece K I J (n + 1)) :
    quotientDegreePiece K I J n = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact quotientDegreePiece_constant K I J n a
  | add p q hp hq =>
    rw [map_add]
    exact (quotientDegreePiece K I J n).add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, h]
    exact quotientDegreePiece_mul_variable K I J n i _ hp

end FLT.Mazur.HilbertChart
