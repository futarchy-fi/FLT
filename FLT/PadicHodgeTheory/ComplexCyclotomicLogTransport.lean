/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicLog
public import FLT.PadicHodgeTheory.ComplexThetaEquivariance

/-! # Transport of the actual cyclotomic logarithmic sum

The result is the logarithm at the transformed argument. Identifying it
with the cyclotomic scalar times t is a further analytic theorem.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Ring endomorphisms fix the genuine inverse of each positive integer. -/
theorem complexDeRham_map_inverse_nat (f : ComplexBDeRhamPlus p →+* ComplexBDeRhamPlus p)
    (n : ℕ) (hn : n ≠ 0) :
    f (Ring.inverse (n : ComplexBDeRhamPlus p)) = Ring.inverse (n : ComplexBDeRhamPlus p) := by
  apply (complexDeRhamNat_isUnit p n hn).mul_left_cancel
  rw [Ring.mul_inverse_cancel _ (complexDeRhamNat_isUnit p n hn)]
  calc
    (n : ComplexBDeRhamPlus p) * f (Ring.inverse (n : ComplexBDeRhamPlus p)) =
        f ((n : ComplexBDeRhamPlus p) * Ring.inverse (n : ComplexBDeRhamPlus p)) := by
      rw [map_mul, map_natCast]
    _ = 1 := by rw [Ring.mul_inverse_cancel _ (complexDeRhamNat_isUnit p n hn), map_one]

/-- In particular all logarithm coefficients are fixed by the actual Galois action. -/
@[simp] theorem complexLogCoefficient_galois (σ : PadicGalois p) (n : ℕ) :
    complexDeRhamGalois p σ (complexLogCoefficient p n) = complexLogCoefficient p n := by
  cases n with
  | zero => exact map_zero _
  | succ n =>
    unfold complexLogCoefficient
    rw [map_mul, map_pow, map_neg, map_one]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_one] using
      complexDeRham_map_inverse_nat p (complexDeRhamGalois p σ) (n + 1) (Nat.succ_ne_zero n)

/-- The transformed argument is [sigma(epsilon)] - 1 in the actual completion. -/
theorem complexCyclotomicArgument_galois (σ : PadicGalois p) :
    complexDeRhamGalois p σ (complexCyclotomicArgument p) =
      algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)
        (algebraMap (Ainf p) (ComplexAinfInvertP p)
          (WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p)) - 1)) := by
  rw [complexCyclotomicArgument, complexDeRhamGalois_algebraMap,
    complexLocalizedGalois_algebraMap]
  congr 2
  simp [complexCyclotomicDifference, complexAinfGalois]

/-- All terms at the transformed argument satisfy the same adic bounds. -/
theorem complexCyclotomicLog_transformed_term_mem (σ : PadicGalois p) (n : ℕ) :
    complexLogCoefficient p n * (complexDeRhamGalois p σ (complexCyclotomicArgument p)) ^ n ∈
      Ideal.span {complexDeRhamParameter p} ^ n := by
  have h : complexDeRhamGalois p σ (complexCyclotomicArgument p) ∈
      Ideal.span {complexDeRhamParameter p} :=
    complexDeRhamGalois_ideal p σ (complexCyclotomicArgument_mem p)
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow h n)

/-- Galois carries t to the actual adic logarithm of the transformed Teichmuller element. -/
theorem complexCyclotomicLog_galois_sum (σ : PadicGalois p) :
    complexDeRhamGalois p σ (complexCyclotomicLog p) =
      adicSeries (Ideal.span {complexDeRhamParameter p})
        (fun n ↦ complexLogCoefficient p n *
          (complexDeRhamGalois p σ (complexCyclotomicArgument p)) ^ n)
        (complexCyclotomicLog_transformed_term_mem p σ) := by
  unfold complexCyclotomicLog
  rw [adicSeries_map _ _ (complexDeRhamGalois_ideal p σ)]
  simp only [map_mul, map_pow, complexLogCoefficient_galois]

end PadicHodgeTheory
