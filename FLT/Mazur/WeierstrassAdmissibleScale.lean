/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Recovering an admissible scale from the two leading units

The relation w squared equals s cubed determines the unique scale u = w/s.
No roots are adjoined and no residue characteristics are excluded.
-/

@[expose] public section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R]

/-- The quotient of the leading units is a square root of the x scale. -/
theorem admissibleScale_sq (s w : Rˣ) (h : (w : R) ^ 2 = (s : R) ^ 3) :
    ((w / s : Rˣ) : R) ^ 2 = (s : R) := by
  have hu : w ^ 2 = s ^ 3 := Units.ext h
  have he : (w / s) ^ 2 = s := by
    rw [div_pow, hu]
    rw [pow_succ, mul_comm, mul_div_cancel_right]
  exact congrArg Units.val he

/-- The same quotient is a cube root of the y scale. -/
theorem admissibleScale_cube (s w : Rˣ) (h : (w : R) ^ 2 = (s : R) ^ 3) :
    ((w / s : Rˣ) : R) ^ 3 = (w : R) := by
  have hu : w ^ 2 = s ^ 3 := Units.ext h
  have he : (w / s) ^ 3 = w := by
    calc
      (w / s) ^ 3 = w * (w ^ 2 / s ^ 3) := by
        rw [div_pow, pow_succ w 2, mul_comm (w ^ 2), mul_div_assoc]
      _ = w := by rw [hu]; simp
  exact congrArg Units.val he

/-- The two leading coefficients uniquely determine the admissible unit. -/
theorem admissibleScale_unique (s w u : Rˣ)
    (hs : (u : R) ^ 2 = (s : R)) (hw : (u : R) ^ 3 = (w : R)) : u = w / s := by
  have hs' : u ^ 2 = s := Units.ext hs
  have hw' : u ^ 3 = w := Units.ext hw
  rw [← hs', ← hw']
  rw [pow_succ, mul_comm, mul_div_cancel_right]

/-- Recover the admissible change directly from triangular coefficients. -/
def triangularVariableChange (r t v : R) (s w : Rˣ) : VariableChange R :=
  ⟨w / s, r, (↑s⁻¹ : R) * v, t⟩

/-- Its x coefficient is exactly the original leading x unit. -/
theorem triangularVariableChange_x (r t v : R) (s w : Rˣ)
    (h : (w : R) ^ 2 = (s : R) ^ 3) :
    ((triangularVariableChange r t v s w).u : R) ^ 2 = (s : R) :=
  admissibleScale_sq s w h

/-- Its y coefficient is exactly the original leading y unit. -/
theorem triangularVariableChange_y (r t v : R) (s w : Rˣ)
    (h : (w : R) ^ 2 = (s : R) ^ 3) :
    ((triangularVariableChange r t v s w).u : R) ^ 3 = (w : R) :=
  admissibleScale_cube s w h

/-- Its mixed coefficient recovers the original coefficient of x in y. -/
theorem triangularVariableChange_mixed (r t v : R) (s w : Rˣ)
    (h : (w : R) ^ 2 = (s : R) ^ 3) :
    ((triangularVariableChange r t v s w).u : R) ^ 2 *
      (triangularVariableChange r t v s w).s = v := by
  rw [triangularVariableChange_x r t v s w h]
  change (s : R) * ((↑s⁻¹ : R) * v) = v
  rw [← mul_assoc, s.mul_inv, one_mul]

end FLT.Mazur.WeierstrassIntegralChart
