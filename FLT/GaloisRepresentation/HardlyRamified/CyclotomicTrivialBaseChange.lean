/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialPolynomial
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # The common rational polynomial after coefficient extension

The characteristic-polynomial formula holds after scalar extension and any
chosen framing. No equivalence with an original nonsplit member is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation
open Polynomial
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
  (A : Type*) [Field A] [TopologicalSpace A] [IsTopologicalRing A]
  [Algebra ℤ_[p] A] [ContinuousSMul ℤ_[p] A]

/-- Scalar extension preserves the standard member's explicit polynomial. -/
theorem cyclotomicTrivial_baseChange_charpoly (g : Field.absoluteGaloisGroup ℚ) :
    ((cyclotomicTrivial p).baseChange A g).charpoly =
      (X - 1) * (X - C (algebraMap ℤ_[p] A (integralCyclotomicScalar p g))) := by
  change ((cyclotomicTrivial p g).baseChange A).charpoly = _
  rw [LinearMap.charpoly_baseChange, cyclotomicTrivial_charpoly]
  simp

/-- The Frobenius polynomial is the image of the common rational polynomial. -/
theorem cyclotomicTrivial_baseChange_frobenius (φ : ℚ →+* A)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    (((cyclotomicTrivial p).baseChange A).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
      (cyclotomicTrivialPolynomial q).map φ := by
  change LinearMap.charpoly
    (((cyclotomicTrivial p).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).baseChange
        A) = _
  rw [LinearMap.charpoly_baseChange, cyclotomicTrivial_frobenius_charpoly p q hq hqp]
  simp [cyclotomicTrivialPolynomial]

/-- Framing does not alter the common rational Frobenius polynomial. -/
theorem cyclotomicTrivial_framed_frobenius (φ : ℚ →+* A)
    (e : A ⊗[ℤ_[p]] (ℤ_[p] × ℤ_[p]) ≃ₗ[A] (Fin 2 → A))
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    ((((cyclotomicTrivial p).baseChange A).conj e).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
      (cyclotomicTrivialPolynomial q).map φ := by
  change (e.conj _).charpoly = _
  rw [LinearEquiv.charpoly_conj]
  exact cyclotomicTrivial_baseChange_frobenius p A φ q hq hqp

end GaloisRepresentation
