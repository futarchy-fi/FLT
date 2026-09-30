/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The equation of the split node

The actual ring of pairs with equal constant terms is the quotient by `xy`.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PolygonNodePresentation

open PolygonNodeEqualizer PolygonNodeLocalization

variable {R : Type*} [CommRing R]

/-- Evaluate the two plane coordinates on the two branches. -/
def aPresent : MvPolynomial (Fin 2) R →ₐ[R] A (R := R) :=
  MvPolynomial.aeval ![x, y]

@[simp] theorem aPresent_X_zero : aPresent (MvPolynomial.X 0) = x (R := R) := by
  simp [aPresent]

@[simp] theorem aPresent_X_one : aPresent (MvPolynomial.X 1) = y (R := R) := by
  simp [aPresent]

/-- Every node function is a polynomial in the branch coordinates. -/
theorem aPresent_surjective : Function.Surjective (aPresent (R := R)) := by
  rw [← AlgHom.range_eq_top, aPresent, ← Algebra.adjoin_range_eq_range_aeval]
  simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] using (a_adjoin (R := R))

/-- Orthogonal coordinates kill all nonconstant terms on the other branch. -/
theorem mul_aeval_of_mul_eq_zero {S : Type*} [CommRing S] [Algebra R S]
    (a b : S) (h : a * b = 0) (p : R[X]) :
    a * aeval b p = a * algebraMap R S (p.eval 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, mul_add, eval_add, hp, hq]
  | monomial n r =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [aeval_monomial, eval_monomial, zero_pow (Nat.succ_ne_zero n),
        mul_zero, map_zero, pow_succ']
      calc
        a * (algebraMap R S r * (b * b ^ n)) = (a * b) *
          (algebraMap R S r * b ^ n) := by ring
        _ = 0 := by rw [h, zero_mul]

/-- The defining ideal of the split plane node. -/
def aRelation : Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

/-- Modulo `xy`, a polynomial is recovered from its two branch restrictions. -/
theorem a_normalForm (p : MvPolynomial (Fin 2) R) :
    let q := Ideal.Quotient.mkₐ R (aRelation (R := R))
    q p = aeval (q (MvPolynomial.X 0)) (first (aPresent p)) +
      aeval (q (MvPolynomial.X 1)) (second (aPresent p)) -
      algebraMap R _ (aEval (aPresent p)) := by
  let q := Ideal.Quotient.mkₐ R (aRelation (R := R))
  have hxy : q (MvPolynomial.X 0) * q (MvPolynomial.X 1) = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  change q p = _
  induction p using MvPolynomial.induction_on with
  | C r => simp [aPresent, aEval]
  | add p r hp hr => simp only [map_add, hp, hr]; ring
  | mul_X p i hp =>
    fin_cases i
    · simp only [map_mul]
      simp only [Fin.zero_eta, Fin.isValue, Ideal.Quotient.mkₐ_eq_mk,
        aPresent_X_zero, first_x, aeval_X, second_x, map_zero, mul_zero, add_zero]
      rw [hp]
      have hm := mul_aeval_of_mul_eq_zero (q (MvPolynomial.X 0))
        (q (MvPolynomial.X 1)) hxy (second (aPresent p))
      have he : (second (aPresent p)).eval 0 = aEval (aPresent p) :=
        (aPresent p).property.symm
      simp only [he] at hm
      simp only [aeval_def] at hm
      simp only [aEval, AlgHom.comp_apply, aeval_def]
      simp [q, aPresent, aEval, ← coeff_zero_eq_eval_zero] at hm ⊢
      linear_combination hm
    · simp only [map_mul]
      simp only [Fin.mk_one, Fin.isValue, Ideal.Quotient.mkₐ_eq_mk,
        aPresent_X_one, first_y, map_zero, mul_zero, second_y, aeval_X, zero_add]
      rw [hp]
      have hm := mul_aeval_of_mul_eq_zero (q (MvPolynomial.X 1))
        (q (MvPolynomial.X 0)) (by simpa [mul_comm] using hxy) (first (aPresent p))
      simp only [aeval_def, aEval, AlgHom.comp_apply]
      simp only [aeval_def] at hm
      simp [q, aPresent, ← coeff_zero_eq_eval_zero] at hm ⊢
      linear_combination hm

/-- There are no additional equations in the equalizer ring. -/
theorem aPresent_ker : RingHom.ker (aPresent (R := R)).toRingHom = aRelation := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := a_normalForm p
    have hp' : aPresent p = 0 := hp
    simpa only [hp', map_zero, zero_add, sub_zero, Ideal.Quotient.mkₐ_eq_mk] using h
  · rw [aRelation, Ideal.span_le, Set.singleton_subset_iff]
    change aPresent (MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp

/-- The plane equation presents the actual equalizer algebra. -/
def aQuotientEquiv : (MvPolynomial (Fin 2) R ⧸ aRelation) ≃ₐ[R] A (R := R) :=
  (Ideal.quotientEquivAlgOfEq R aPresent_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective aPresent_surjective)

end FLT.Mazur.PolygonNodePresentation
