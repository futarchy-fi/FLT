/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicAction
public import FLT.PadicHodgeTheory.ComplexCyclotomicShift

/-! # Actual shifted roots for cyclotomic integer approximants -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The natural integer representative of the actual cyclotomic character modulo p^n. -/
def complexCyclotomicExponent (σ : PadicGalois p) (n : ℕ) : ℕ :=
  ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val.toZModPow n).val

/-- Removing all n shifts by the p^n-th power recovers epsilon. -/
theorem complexCyclotomicShift_pow_prime_pow (n : ℕ) :
    complexCyclotomicShift p n ^ (p ^ n) = complexCyclotomicTilt p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, complexCyclotomicShift_pow, ih]

/-- The two shifted Teichmuller roots have exactly the same theta image. -/
theorem complexCyclotomicApproximation_root_sub_mem (σ : PadicGalois p) (n : ℕ) :
    WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicShift p n)) -
      WittVector.teichmuller p (complexCyclotomicShift p n) ^
        complexCyclotomicExponent p σ n ∈ RingHom.ker (complexTheta p) := by
  change complexTheta p _ = 0
  rw [map_sub, map_pow, complexTheta_teichmuller, complexTheta_teichmuller,
    complexSharp_equivariant, complexCyclotomicShift_sharp,
    complexCyclotomicSequence_action]
  exact sub_self _

/-- The transformed shifted root has the required actual Galois endpoint. -/
theorem complexCyclotomicApproximation_galois_pow (σ : PadicGalois p) (n : ℕ) :
    WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicShift p n)) ^
        (p ^ n) =
      WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p)) := by
  rw [← map_pow, ← map_pow, complexCyclotomicShift_pow_prime_pow]

/-- The other shifted root has the integer-power approximant as endpoint. -/
theorem complexCyclotomicApproximation_integer_pow (σ : PadicGalois p) (n : ℕ) :
    (WittVector.teichmuller p (complexCyclotomicShift p n) ^
        complexCyclotomicExponent p σ n) ^ (p ^ n) =
      WittVector.teichmuller p (complexCyclotomicTilt p) ^
        complexCyclotomicExponent p σ n := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, ← map_pow,
    complexCyclotomicShift_pow_prime_pow]

end PadicHodgeTheory
