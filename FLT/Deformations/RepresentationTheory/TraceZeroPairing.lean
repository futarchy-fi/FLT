/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.MatrixTangentTrace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Nondegeneracy of the trace-zero adjoint pairing

The pairing is the actual matrix trace of a product. It is invariant under
the specified conjugation action and is nondegenerate in dimension two
when two is nonzero in the coefficient field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Deformation
variable {k G n : Type*} [CommRing k] [Group G] [Fintype n] [DecidableEq n]
  (r : G →* GL n k)

/-- Matrix multiplication with its matrix type explicit across the adjoint type alias. -/
abbrev adjointMatrixProduct (X Y : Matrix n n k) : Matrix n n k := X * Y

/-- The bilinear trace pairing on the original trace-zero adjoint module. -/
def traceZeroPairing : traceZeroAdjoint r →ₗ[k] Module.Dual k (traceZeroAdjoint r) where
  toFun X :=
    { toFun := fun Y ↦ Matrix.trace (adjointMatrixProduct X.val Y.val)
      map_add' := fun Y Z ↦
        (congrArg Matrix.trace (Matrix.mul_add X.val Y.val Z.val)).trans (Matrix.trace_add _ _)
      map_smul' := fun a Y ↦
        (congrArg Matrix.trace (Matrix.mul_smul X.val a Y.val)).trans (Matrix.trace_smul _ _) }
  map_add' X Y := by
    ext Z
    exact (congrArg Matrix.trace (Matrix.add_mul X.val Y.val Z.val)).trans (Matrix.trace_add _ _)
  map_smul' a X := by
    ext Y
    exact (congrArg Matrix.trace (Matrix.smul_mul a X.val Y.val)).trans (Matrix.trace_smul _ _)

/-- The pairing is symmetric. -/
theorem traceZeroPairing_symm (X Y : traceZeroAdjoint r) :
    traceZeroPairing r X Y = traceZeroPairing r Y X :=
  Matrix.trace_mul_comm _ _

/-- Simultaneous conjugation preserves the trace pairing. -/
theorem traceZeroPairing_invariant (g : G) (X Y : traceZeroAdjoint r) :
    traceZeroPairing r (g • X) (g • Y) = traceZeroPairing r X Y := by
  change Matrix.trace (adjointMatrixProduct
    (adjointMatrixProduct (adjointMatrixProduct (r g).val X.val) (r g)⁻¹.val)
    (adjointMatrixProduct (adjointMatrixProduct (r g).val Y.val) (r g)⁻¹.val)) = _
  have he : adjointMatrixProduct
      (adjointMatrixProduct (adjointMatrixProduct (r g).val X.val) (r g)⁻¹.val)
      (adjointMatrixProduct (adjointMatrixProduct (r g).val Y.val) (r g)⁻¹.val) =
        adjointMatrixProduct
          (adjointMatrixProduct (r g).val (adjointMatrixProduct X.val Y.val)) (r g)⁻¹.val := by
    simp [adjointMatrixProduct, Matrix.mul_assoc]
  rw [he]
  exact Matrix.trace_units_conj (r g) _

end Deformation

namespace Deformation
variable {k G : Type*} [Field k] [Group G] (r : G →* GL (Fin 2) k)

/-- Explicit test vectors in the actual trace-zero adjoint. -/
def traceZeroTest (a b c : k) : traceZeroAdjoint r :=
  ⟨!![a, b; c, -a], by
    change Matrix.trace !![a, b; c, -a] = 0
    simp [Matrix.trace, Fin.sum_univ_two]⟩

/-- Orthogonality to every trace-zero matrix forces a matrix to vanish when two is invertible. -/
theorem traceZeroPairing_nondegenerate (h2 : (2 : k) ≠ 0) (X : traceZeroAdjoint r)
    (hX : ∀ Y, traceZeroPairing r X Y = 0) : X = 0 := by
  have h01 : X.val 0 1 = 0 := by
    simpa [traceZeroPairing, traceZeroTest, adjointMatrixProduct, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] using hX (traceZeroTest r 0 0 1)
  have h10 : X.val 1 0 = 0 := by
    simpa [traceZeroPairing, traceZeroTest, adjointMatrixProduct, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] using hX (traceZeroTest r 0 1 0)
  have hd : X.val 0 0 - X.val 1 1 = 0 := by
    simpa [traceZeroPairing, traceZeroTest, adjointMatrixProduct, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg] using
        hX (traceZeroTest r 1 0 0)
  have ht : X.val 0 0 + X.val 1 1 = 0 := by
    have ht := X.property
    change Matrix.trace (X.val : Matrix (Fin 2) (Fin 2) k) = 0 at ht
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using ht
  have h00 : X.val 0 0 = 0 := by
    apply (mul_eq_zero.mp (show (2 : k) * X.val 0 0 = 0 from by
      linear_combination hd + ht)).resolve_left h2
  have h11 : X.val 1 1 = 0 := by simpa [h00] using ht
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

/-- Nondegeneracy is the injectivity of the map to the actual linear dual. -/
theorem traceZeroPairing_injective (h2 : (2 : k) ≠ 0) :
    Function.Injective (traceZeroPairing r) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro X hX
  change X = 0
  apply traceZeroPairing_nondegenerate r h2 X
  intro Y
  exact congrArg (fun f : Module.Dual k (traceZeroAdjoint r) ↦ f Y) hX

end Deformation
