/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.MatrixAdjointCocycle
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.Ring

/-!
# Fixed determinant and trace-zero normalized derivatives

For two-dimensional matrices, the linearized determinant is the determinant
times the trace of the normalized derivative. Thus fixed-determinant tangent
vectors lie in the actual trace-zero adjoint submodule.
-/

@[expose] public noncomputable section
namespace Deformation
variable {k : Type*} [CommRing k]

/-- The trace of the right-normalized matrix derivative, in dimension two. -/
theorem trace_normalizedMatrixDerivative_two (U : GL (Fin 2) k)
    (D : Matrix (Fin 2) (Fin 2) k) :
    Matrix.trace (D * U⁻¹.val) = Ring.inverse U.val.det *
      (U 0 0 * D 1 1 + U 1 1 * D 0 0 - (U 0 1 * D 1 0 + U 1 0 * D 0 1)) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- The actual determinant equation forces trace zero, without dividing in the base ring. -/
theorem trace_normalizedMatrixDerivative_eq_zero (U : GL (Fin 2) k)
    (D : Matrix (Fin 2) (Fin 2) k)
    (hD : U 0 0 * D 1 1 + U 1 1 * D 0 0 - (U 0 1 * D 1 0 + U 1 0 * D 0 1) = 0) :
    Matrix.trace (D * U⁻¹.val) = 0 := by
  rw [trace_normalizedMatrixDerivative_two, hD, mul_zero]

variable {G n : Type*} [Group G] [Fintype n] [DecidableEq n] (r : G →* GL n k)

/-- The trace-zero submodule of the specified adjoint coefficients. -/
def traceZeroAdjoint : Submodule k (AdjointMatrices r) :=
  (show AdjointMatrices r →ₗ[k] k from Matrix.traceLinearMap n k k).ker

/-- Conjugation preserves this submodule. -/
theorem traceZeroAdjoint_smul (g : G) {X : AdjointMatrices r}
    (hX : X ∈ traceZeroAdjoint r) : g • X ∈ traceZeroAdjoint r := by
  change Matrix.trace (show Matrix n n k from (g • X : AdjointMatrices r)) = 0
  exact (AdjointMatrices.trace_smul r g X).trans hX

/-- The trace-zero coefficients carry the restricted adjoint action. -/
instance traceZeroAdjointDistribMulAction : DistribMulAction G (traceZeroAdjoint r) where
  smul g X := ⟨g • X.val, traceZeroAdjoint_smul r g X.property⟩
  one_smul X := Subtype.ext (one_smul G X.val)
  mul_smul g h X := Subtype.ext (mul_smul g h X.val)
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g X Y := Subtype.ext (smul_add g X.val Y.val)

end Deformation
