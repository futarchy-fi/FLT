/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.LinearCombination

/-! # Scalar transfer and trace identities for trivial quotients

These elementary algebra lemmas transfer scalar trace values between coefficient
fields and compute the trace of an endomorphism with a trivial quotient in dimension two.
-/

@[expose] public section

namespace GaloisRepresentation.B5Inputs

/-- A scalar equal to `1 + q` in one coefficient field has the same value in another. -/
theorem trace_scalar_transfer {E A B Kp K3 : Type*} [Field E] [CommRing A] [CommRing B]
    [Field Kp] [Field K3] (ψ : E →+* Kp) (φ : E →+* K3)
    (iA : A →+* Kp) (hi : Function.Injective iA)
    (iB : B →+* K3) (a : E) (x : A) (y : B) (q : ℕ)
    (hx : iA x = ψ a) (hy : iB y = φ a) (ht : y = 1 + q) :
    x = 1 + q := by
  have ha : a = 1 + q := φ.injective (by rw [← hy, ht]; simp)
  apply hi
  rw [hx, ha]
  simp

/-- A two-by-two matrix acting trivially on its second-coordinate quotient has
trace equal to one plus its determinant. -/
theorem trace_eq_one_add_det_of_matrix_trivial_quotient {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (h₁₀ : M 1 0 = 0) (h₁₁ : M 1 1 = 1) :
    M.trace = 1 + M.det := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two, h₁₀, h₁₁, add_comm]

/-- A two-dimensional endomorphism with a trivial one-dimensional quotient has
trace equal to one plus its determinant. -/
theorem trace_eq_one_add_det_of_trivial_quotient {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (A : Module.End K V) (π : V →ₗ[K] K)
    (hs : Function.Surjective π) (hπ : π.comp A = π) :
    LinearMap.trace K V A = 1 + LinearMap.det A := by
  have hsing : (A - 1).det = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hker
    have hsurj : Function.Surjective (A - 1 : Module.End K V) :=
      LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)
    obtain ⟨v, hv⟩ := hs 1
    obtain ⟨w, hw⟩ := hsurj v
    have hwπ : π (A w) = π w := LinearMap.congr_fun hπ w
    have : (0 : K) = 1 := by
      calc
        0 = π ((A - 1) w) := by simp [hwπ]
        _ = 1 := by rw [hw, hv]
    exact zero_ne_one this
  let b := Module.finBasisOfFinrankEq K V hV
  rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.det_toMatrix b]
  rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one] at hsing
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply,
    Matrix.one_apply, Fin.isValue, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    Nat.reduceEqDiff, ↓reduceIte] at hsing ⊢
  linear_combination -hsing

end GaloisRepresentation.B5Inputs
