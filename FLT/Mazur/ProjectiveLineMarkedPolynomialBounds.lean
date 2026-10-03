/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineMarkedSectionTransition
public import Mathlib.RingTheory.Polynomial.DegreeLT
/-!
# Bounded polynomials of actual marked divisor sections

The Laurent transition forces degree at most the divisor multiplicity on both
charts. Coefficient reversal includes the marking unit. The normalized right
endpoint polynomial value is the top left coefficient; identifying it with an
intrinsic node fiber and constructing sections from polynomials remain separate.
-/

open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
namespace FLT.Mazur.ProjectiveLineMarkedPolynomialBounds
open LaurentPolynomial Polynomial
variable {K : Type*} [Field K]
/-- Polynomial inclusion preserves coefficients at natural exponents. -/
lemma coeff_toLaurent_nat (p : K[X]) (n : ℕ) : (toLaurent p).coeff (n : ℤ) = p.coeff n := by
  change (Finsupp.mapDomain Nat.castEmbedding p.toFinsupp.coeff) (Nat.castEmbedding n) = _
  rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective,
    Polynomial.toFinsupp_apply]
/-- A polynomial has no negative Laurent coefficients. -/
lemma coeff_toLaurent_neg (p : K[X]) {z : ℤ} (hz : z < 0) :
    (toLaurent p).coeff z = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨n, hn⟩
  change (n : ℤ) = z at hn
  omega
/-- The powered transition shifts coefficients and multiplies by its coefficient unit. -/
lemma transition_coeff (a : Kˣ) (m : ℕ) (p : K[X]) (z : ℤ) :
    ((ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p).coeff z =
      (↑((-a)⁻¹) : K) ^ m * (toLaurent p).coeff (z + m) := by
  change ((LaurentPolynomial.C (↑((-a)⁻¹) : K) * T (-1)) ^ m * toLaurent p).coeff z = _
  rw [mul_pow, ← map_pow, T_pow, ← single_eq_C_mul_T]
  apply AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff
  intro z' _
  constructor <;> intro h <;> omega
/-- Compatible polynomial coordinates satisfy weighted coefficient reversal. -/
lemma coefficient_relation (a : Kˣ) (m : ℕ) {p q : K[X]}
    (h : invert (toLaurent q) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p)
    (n : ℕ) (hn : n ≤ m) :
    q.coeff n = (↑((-a)⁻¹) : K) ^ m * p.coeff (m - n) := by
  have hh := congrArg (fun f : K[T;T⁻¹] ↦ f.coeff (-(n : ℤ))) h
  rw [invert_apply, neg_neg, coeff_toLaurent_nat, transition_coeff] at hh
  have he : -(n : ℤ) + m = ((m - n : ℕ) : ℤ) := by omega
  rw [he, coeff_toLaurent_nat] at hh
  exact hh
/-- A compatible left coordinate vanishes above the divisor multiplicity. -/
lemma left_coeff_vanish (a : Kˣ) (m : ℕ) {p q : K[X]}
    (h : invert (toLaurent q) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p)
    (n : ℕ) (hn : m < n) : p.coeff n = 0 := by
  have hh := congrArg (fun f : K[T;T⁻¹] ↦ f.coeff ((n : ℤ) - m)) h
  rw [invert_apply, coeff_toLaurent_neg q (by omega), transition_coeff] at hh
  rw [sub_add_cancel, coeff_toLaurent_nat] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ (Units.ne_zero _))
/-- A compatible right coordinate vanishes above the divisor multiplicity. -/
lemma right_coeff_vanish (a : Kˣ) (m : ℕ) {p q : K[X]}
    (h : invert (toLaurent q) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p)
    (n : ℕ) (hn : m < n) : q.coeff n = 0 := by
  have hh := congrArg (fun f : K[T;T⁻¹] ↦ f.coeff (-(n : ℤ))) h
  rw [invert_apply, neg_neg, coeff_toLaurent_nat, transition_coeff,
    coeff_toLaurent_neg p (by omega), mul_zero] at hh
  exact hh
/-- The left coordinate is a bounded polynomial. -/
lemma left_mem_degreeLT (a : Kˣ) (m : ℕ) {p q : K[X]}
    (h : invert (toLaurent q) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p) :
    p ∈ degreeLT K (m + 1) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro n hn
  exact left_coeff_vanish a m h n (by omega)
/-- The right coordinate is a bounded polynomial. -/
lemma right_mem_degreeLT (a : Kˣ) (m : ℕ) {p q : K[X]}
    (h : invert (toLaurent q) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m * toLaurent p) :
    q ∈ degreeLT K (m + 1) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro n hn
  exact right_coeff_vanish a m h n (by omega)

open CategoryTheory AlgebraicGeometry FCurve ProjectiveLineMarkedSectionTransition
variable (K)
/-- The actual left polynomial has degree at most the divisor multiplicity. -/
lemma leftPolynomial_bounded (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    leftPolynomial K a m s ∈ degreeLT K (m + 1) :=
  left_mem_degreeLT a m (transition K a m s)
/-- The actual right polynomial has degree at most the divisor multiplicity. -/
lemma rightPolynomial_bounded (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    rightPolynomial K a m s ∈ degreeLT K (m + 1) :=
  right_mem_degreeLT a m (transition K a m s)
/-- Actual section coordinates satisfy weighted coefficient reversal. -/
lemma rightPolynomial_coeff (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m)
    (n : ℕ) (hn : n ≤ m) :
    (rightPolynomial K a m s).coeff n =
      (↑((-a)⁻¹) : K) ^ m * (leftPolynomial K a m s).coeff (m - n) :=
  coefficient_relation a m (transition K a m s) n hn
/-- The right coordinate at zero is a unit multiple of the top left coefficient. -/
lemma rightPolynomial_eval_zero (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    (rightPolynomial K a m s).eval 0 =
      (↑((-a)⁻¹) : K) ^ m * (leftPolynomial K a m s).coeff m := by
  simpa only [Polynomial.coeff_zero_eq_eval_zero, Nat.sub_zero] using
    rightPolynomial_coeff K a m s 0 (Nat.zero_le m)
/-- Dividing by the right canonical endpoint value gives the top left coefficient. -/
lemma rightPolynomial_endpoint_ratio (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    (rightPolynomial K a m s).eval 0 / (-((↑a⁻¹) : K)) ^ m =
      (leftPolynomial K a m s).coeff m := by
  rw [rightPolynomial_eval_zero]
  have hu : (↑((-a)⁻¹) : K) = -(↑a⁻¹ : K) := by simp
  rw [hu, mul_div_cancel_left₀ _ (pow_ne_zero _ (neg_ne_zero.mpr (Units.ne_zero _)))]
end FLT.Mazur.ProjectiveLineMarkedPolynomialBounds
