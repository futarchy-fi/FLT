/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudUniversalCharacterConstant
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# Universal constants in the additive group algebra

The reduced character average is an explicit element of the group algebra
of the additive finite field. Its powers evaluate to the universal constants.
In characteristic p its p-th power vanishes by the Frobenius identity.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R F : Type*} [CommRing R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)]

/-- The formal reduced average, independent of every finite-flat model. -/
def formalAverage (χ : Fˣ →* Rˣ) : AddMonoidAlgebra R F :=
  ⅟(Fintype.card Fˣ : R) • ∑ u : Fˣ,
    (↑(χ u)⁻¹ : R) • (AddMonoidAlgebra.single (u : F) 1 - 1)

/-- Evaluate a formal scalar combination on an arbitrary scalar-valued function. -/
def evaluate (f : F → R) : AddMonoidAlgebra R F →ₗ[R] R :=
  (Finsupp.linearCombination R f).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The finite-difference recursion is evaluation of the formal average's powers. -/
theorem constant_eq_formalAverage (χ ψ : Fˣ →* Rˣ) (n : ℕ) :
    constant χ ψ n = evaluate (value ψ) (formalAverage χ ^ n) := by
  let s : F → AddMonoidAlgebra R F := fun a ↦ AddMonoidAlgebra.single a 1
  have hs (a b : F) : s (a + b) = s a * s b := by
    simp [s, AddMonoidAlgebra.single_mul_single]
  have he := iterate_eq_pow_mul χ s hs n 0
  have he' : iterate χ s n 0 = formalAverage χ ^ n := by
    simpa only [s, ← AddMonoidAlgebra.one_def, one_mul, formalAverage] using he
  rw [constant, ← he', map_iterate]
  congr 1
  funext a
  simp [s, evaluate]

/-- In matching positive characteristic the formal p-fold average is zero. -/
theorem formalAverage_pow_char (p : ℕ) [Fact p.Prime] [CharP F p] [CharP R p]
    (χ : Fˣ →* Rˣ) : formalAverage χ ^ p = 0 := by
  let : CharP (AddMonoidAlgebra R F) p := charP_of_injective_algebraMap' R p
  have hu (u : Fˣ) : (AddMonoidAlgebra.single (u : F) (1 : R) - 1) ^ p = 0 := by
    rw [sub_pow_char, AddMonoidAlgebra.single_pow, one_pow, one_pow]
    simp [nsmul_eq_mul, CharP.cast_eq_zero, ← AddMonoidAlgebra.one_def]
  simp only [formalAverage, smul_pow, sum_pow_char]
  simp only [hu, smul_zero, Finset.sum_const_zero]

/-- The universal p-fold constant vanishes in matching characteristic p. -/
theorem constant_char (p : ℕ) [Fact p.Prime] [CharP F p] [CharP R p]
    (χ ψ : Fˣ →* Rˣ) : constant χ ψ p = 0 := by
  rw [constant_eq_formalAverage, formalAverage_pow_char, map_zero]

end ThreeAdicPlan.CharacterAverage
