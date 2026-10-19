/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericQuadraticRelation

/-!
# The full function-field map of the original Vélu formulas

The actual x substitution and completed y-coordinate define an injective map
from the target quadratic function field into the source function field. The
construction retains the original coordinate formulas and all coefficients.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The actual target function field maps to the source by the original Vélu formulas. -/
def veluGenericFunctionFieldHom : FunctionField (curve E G) →ₐ[K] FunctionField E := by
  let _ : Algebra K⟮X⟯ (FunctionField E) := (veluGenericXFieldHom E G).toRingHom.toAlgebra
  let f := @QuadraticAlgebra.lift K⟮X⟯ (cubicFunction (curve E G)) 0 _
    (FunctionField E) _ (veluGenericXFieldHom E G).toRingHom.toAlgebra
      ⟨veluGenericCompletedY E G, by
        change veluGenericCompletedY E G * veluGenericCompletedY E G =
          veluGenericXFieldHom E G (cubicFunction (curve E G)) * 1 +
            veluGenericXFieldHom E G 0 * veluGenericCompletedY E G
        simpa only [map_zero, zero_mul, add_zero, mul_one] using
          veluGenericCompletedY_sq E G hodd⟩
  refine { f.toRingHom with commutes' := fun c ↦ ?_ }
  change veluGenericXFieldHom E G (RatFunc.C c) * 1 +
    veluGenericXFieldHom E G 0 * veluGenericCompletedY E G = _
  rw [map_zero, zero_mul, add_zero, mul_one]
  exact (veluGenericXFieldHom E G).commutes c

/-- Both original quadratic coefficients and the completed y-coordinate are retained. -/
theorem veluGenericFunctionFieldHom_apply (z : FunctionField (curve E G)) :
    veluGenericFunctionFieldHom E G hodd z =
      veluGenericXFieldHom E G z.re +
        veluGenericXFieldHom E G z.im * veluGenericCompletedY E G := by
  change veluGenericXFieldHom E G z.re * 1 +
    veluGenericXFieldHom E G z.im * veluGenericCompletedY E G = _
  rw [mul_one]

/-- The original target quadratic generator maps to the original completed y function. -/
@[simp] theorem veluGenericFunctionFieldHom_omega :
    veluGenericFunctionFieldHom E G hodd QuadraticAlgebra.omega =
      veluGenericCompletedY E G := by
  rw [veluGenericFunctionFieldHom_apply]
  simp

/-- The target rational x-line is mapped by the original x substitution. -/
@[simp] theorem veluGenericFunctionFieldHom_liftX (f : K⟮X⟯) :
    veluGenericFunctionFieldHom E G hodd (liftX (curve E G) f) =
      veluGenericXFieldHom E G f := by
  rw [veluGenericFunctionFieldHom_apply]
  simp [liftX, QuadraticAlgebra.algebraMap_eq]

/-- The target function field embeds into the source function field. -/
theorem veluGenericFunctionFieldHom_injective :
    Function.Injective (veluGenericFunctionFieldHom E G hodd) :=
  (veluGenericFunctionFieldHom E G hodd).injective

end WeierstrassCurve.Velu
