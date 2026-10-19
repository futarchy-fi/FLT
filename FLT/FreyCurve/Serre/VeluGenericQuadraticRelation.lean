/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericXField

/-!
# The original completed Vélu y-coordinate satisfies the quadratic relation

Substituting the actual x function into the target cubic gives the square of
the original slope times the source cubic. This is the relation needed for a
homomorphism from the full target function field.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

include hodd in
/-- The target cubic after the original x substitution is the original squared y function. -/
theorem veluGenericXFieldHom_cubic :
    veluGenericXFieldHom E G (cubicFunction (curve E G)) =
      algebraMap K⟮X⟯ (FunctionField E) (cubicFunction E * slopeFunction E G ^ 2) := by
  have heq : cubicFunction E * slopeFunction E G ^ 2 =
      4 * xFunction E G ^ 3 + C (curve E G).b₂ * xFunction E G ^ 2 +
        2 * C (curve E G).b₄ * xFunction E G + C (curve E G).b₆ := by
    rw [cubicFunction_eq]
    convert rational_equation_coefficients E G hodd using 1
    simp only [curve, b₂, b₄, b₆, map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  have hc (c : K) : veluGenericXFieldHom E G (C c) =
      algebraMap K⟮X⟯ (FunctionField E) (C c) :=
    ((veluGenericXFieldHom E G).commutes c).trans
      (IsScalarTower.algebraMap_apply K K⟮X⟯ (FunctionField E) c)
  rw [heq, cubicFunction_eq (curve E G)]
  simp only [map_add, map_mul, map_pow, map_ofNat, veluGenericXFieldHom_X, liftX]
  rw [hc, hc, hc]

/-- The completed y-coordinate retains the original slope and source quadratic generator. -/
def veluGenericCompletedY : FunctionField E :=
  algebraMap K⟮X⟯ (FunctionField E) (slopeFunction E G) * QuadraticAlgebra.omega

include hodd in
/-- Its actual square is the target cubic evaluated at the original x-coordinate. -/
theorem veluGenericCompletedY_sq :
    veluGenericCompletedY E G * veluGenericCompletedY E G =
      veluGenericXFieldHom E G (cubicFunction (curve E G)) := by
  rw [veluGenericXFieldHom_cubic E G hodd, veluGenericCompletedY]
  rw [mul_mul_mul_comm, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_mul, sq, map_zero, zero_mul, add_zero]
  ring

end WeierstrassCurve.Velu
