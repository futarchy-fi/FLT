/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivial
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusTraces
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Determinant and Frobenius polynomial of the standard integral member -/

@[expose] public noncomputable section
namespace GaloisRepresentation
open Polynomial
variable (p : ℕ) [Fact p.Prime]

/-- The standard action is the product of multiplication on the two summands. -/
theorem cyclotomicTrivial_eq_prodMap (g : Field.absoluteGaloisGroup ℚ) :
    cyclotomicTrivial p g =
      (LinearMap.mulLeft ℤ_[p] (integralCyclotomicScalar p g)).prodMap LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact cyclotomicTrivialEnd_apply p g x

/-- The actual determinant is the integral cyclotomic character. -/
theorem cyclotomicTrivial_det (g : Field.absoluteGaloisGroup ℚ) :
    (cyclotomicTrivial p).det g = integralCyclotomicScalar p g := by
  change (cyclotomicTrivial p g).det = _
  rw [cyclotomicTrivial_eq_prodMap, LinearMap.det_prodMap]
  simp

/-- A scalar acting on the coefficient ring has its expected linear characteristic polynomial. -/
theorem padic_mulLeft_charpoly (a : ℤ_[p]) :
    (LinearMap.mulLeft ℤ_[p] a).charpoly = X - C a := by
  apply Polynomial.funext
  intro t
  rw [LinearMap.eval_charpoly, LinearMap.det_ring]
  simp

/-- The characteristic polynomial retains both the cyclotomic and trivial characters. -/
theorem cyclotomicTrivial_charpoly (g : Field.absoluteGaloisGroup ℚ) :
    (cyclotomicTrivial p g).charpoly =
      (X - 1) * (X - C (integralCyclotomicScalar p g)) := by
  rw [cyclotomicTrivial_eq_prodMap, LinearMap.charpoly_prodMap, padic_mulLeft_charpoly]
  have hi : (LinearMap.id : Module.End ℤ_[p] ℤ_[p]) = 1 := rfl
  rw [hi, LinearMap.charpoly_one]
  simp [mul_comm]

/-- A common rational polynomial for each good rational prime. -/
def cyclotomicTrivialPolynomial (q : ℕ) : ℚ[X] := (X - 1) * (X - C (q : ℚ))

/-- At q distinct from p, the standard member has the common rational Frobenius polynomial. -/
theorem cyclotomicTrivial_frobenius_charpoly (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    ((cyclotomicTrivial p).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
      (X - 1) * (X - C (q : ℤ_[p])) := by
  rw [GaloisRep.toLocal, GaloisRep.map]
  change (cyclotomicTrivial p _).charpoly = _
  rw [cyclotomicTrivial_charpoly]
  have h := B5Inputs.cyclotomicCharacter_adicArithFrob p q hq hqp
  congr 2
  exact congrArg C h

end GaloisRepresentation
