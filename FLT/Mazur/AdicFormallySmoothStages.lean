/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Constructing compatible lifts of smooth points at every adic order

The adjacent quotient kernels are square zero. Formal smoothness therefore
constructs one compatible tower extending a prescribed first-order quotient
point; compatibility is proved, rather than supplied as additional input.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicFormallySmoothStages
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (I : Ideal R)

/-- The actual adjacent positive-power quotient map. -/
def restriction (m : ℕ) : (R ⧸ I ^ (m + 2)) →ₐ[R] R ⧸ I ^ (m + 1) :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))

/-- Every coefficient at one order lifts to the next order. -/
theorem restriction_surjective (m : ℕ) : Function.Surjective (restriction I m) :=
  Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))

/-- The entire adjacent kernel, including mixed products, is square zero. -/
theorem restriction_kernel_square (m : ℕ) :
    RingHom.ker (restriction I m).toRingHom ^ 2 = ⊥ := by
  change RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))) ^ 2 = ⊥
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

variable [Algebra.FormallySmooth R B] (f : B →ₐ[R] R ⧸ I ^ 1)

/-- Recursively lift the original quotient point through the actual square-zero kernels. -/
def stage : (m : ℕ) → B →ₐ[R] R ⧸ I ^ (m + 1)
  | 0 => f
  | m + 1 => Algebra.FormallySmooth.liftOfSurjective (stage m) (restriction I m)
      (restriction_surjective I m) ⟨2, restriction_kernel_square I m⟩

/-- The constructed tower begins at precisely the prescribed quotient point. -/
theorem stage_zero : stage I f 0 = f := rfl

/-- Adjacent lifts retain the whole preceding algebra morphism. -/
theorem restriction_stage (m : ℕ) :
    (restriction I m).comp (stage I f (m + 1)) = stage I f m :=
  Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _

/-- Evaluation of the constructed tower retains every preceding coordinate. -/
theorem restriction_stage_apply (m : ℕ) (b : B) :
    restriction I m (stage I f (m + 1) b) = stage I f m b :=
  AlgHom.congr_fun (restriction_stage I f m) b

end FLT.Mazur.AdicFormallySmoothStages
