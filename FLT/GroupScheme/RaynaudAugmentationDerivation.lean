/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudUniversalConvolutionAlgebra

/-!
# Additive functions as derivations at the augmentation

Evaluation on an additive field function annihilates products of two
augmentation elements. This detects the linear term of a divided power.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R S F : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field F]

/-- The augmentation of the additive group algebra. -/
def augmentation : AddMonoidAlgebra R F →ₐ[R] R := AddMonoidAlgebra.lift R R F 1

/-- Evaluate coefficients against an additive function with values in an R-algebra. -/
def additiveEvaluation (e : F →+ S) : AddMonoidAlgebra R F →ₗ[R] S :=
  (Finsupp.linearCombination R e).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- A group basis element has augmentation one. -/
@[simp] theorem augmentation_single (a : F) (r : R) :
    augmentation (AddMonoidAlgebra.single a r) = r := by simp [augmentation]

/-- Evaluation on a group basis element is the chosen additive function. -/
@[simp] theorem additiveEvaluation_single (e : F →+ S) (a : F) (r : R) :
    additiveEvaluation e (AddMonoidAlgebra.single a r) = r • e a := by
  simp [additiveEvaluation]

/-- The augmentation Leibniz rule follows from additivity in the scalar field. -/
theorem additiveEvaluation_mul (e : F →+ S) (x y : AddMonoidAlgebra R F) :
    additiveEvaluation e (x * y) =
      augmentation x • additiveEvaluation e y + augmentation y • additiveEvaluation e x := by
  induction x using AddMonoidAlgebra.induction_on with
  | of a =>
    induction y using AddMonoidAlgebra.induction_on with
    | of b =>
      change additiveEvaluation e
        (AddMonoidAlgebra.single a 1 * AddMonoidAlgebra.single b 1) = _
      simp [AddMonoidAlgebra.single_mul_single, map_add, add_comm]
    | add y z hy hz =>
      simp only [mul_add, map_add, hy, hz, add_smul, smul_add]
      abel
    | smul r y hy =>
      simp only [mul_smul_comm, map_smul, hy, smul_add, smul_smul, smul_eq_mul]
      simp [mul_comm]
  | add x z hx hz =>
    simp only [add_mul, map_add, hx, hz, add_smul, smul_add]
    abel
  | smul r x hx =>
    simp only [smul_mul_assoc, map_smul, hx, smul_add, smul_smul, smul_eq_mul]
    simp [mul_comm]

/-- Additive evaluation vanishes on products of augmentation elements. -/
theorem additiveEvaluation_mul_eq_zero (e : F →+ S) (x y : AddMonoidAlgebra R F)
    (hx : augmentation x = 0) (hy : augmentation y = 0) :
    additiveEvaluation e (x * y) = 0 := by
  rw [additiveEvaluation_mul, hx, hy, zero_smul, zero_smul, add_zero]

/-- Every power of degree at least two is invisible to additive evaluation. -/
theorem additiveEvaluation_pow_eq_zero (e : F →+ S) (x : AddMonoidAlgebra R F)
    (hx : augmentation x = 0) (n : ℕ) (hn : 2 ≤ n) :
    additiveEvaluation e (x ^ n) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, pow_two, mul_assoc]
  apply additiveEvaluation_mul_eq_zero e _ _ hx
  simp [hx]

end ThreeAdicPlan.CharacterAverage
