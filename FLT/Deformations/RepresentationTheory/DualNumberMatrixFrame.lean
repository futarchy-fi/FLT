/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.MatrixAdjointCocycle
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Actual strict frames over the dual numbers

The matrix `1 + εX` is invertible, reduces to the identity, and conjugation
changes the derivative by `Xρ - ρX`. Right normalization therefore adds the
adjoint coboundary of `-X`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Deformation
open TrivSqZeroExt GaloisRepresentation.Extensions
variable {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n]

/-- A dual-number matrix with specified constant and first-order coefficients. -/
def dualNumberMatrix (A D : Matrix n n k) : Matrix n n (TrivSqZeroExt k k) :=
  fun i j ↦ ⟨A i j, D i j⟩

omit [DecidableEq n] in
/-- Matrix multiplication has the same first-order product rule as the universal derivative. -/
theorem dualNumberMatrix_mul (A D B E : Matrix n n k) :
    dualNumberMatrix A D * dualNumberMatrix B E = dualNumberMatrix (A * B) (A * E + D * B) := by
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · simp [Matrix.mul_apply, dualNumberMatrix, fst_sum, fst_mul]
  · simp [Matrix.mul_apply, dualNumberMatrix, snd_sum, snd_mul, Finset.sum_add_distrib]

omit [Fintype n] in
/-- The identity matrix has zero first-order part. -/
theorem dualNumberMatrix_one : dualNumberMatrix (1 : Matrix n n k) 0 = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [dualNumberMatrix, Matrix.one_apply, h]

/-- The actual strict change of frame, together with its explicit inverse. -/
def dualNumberStrictFrame (X : Matrix n n k) : GL n (TrivSqZeroExt k k) where
  val := dualNumberMatrix 1 X
  inv := dualNumberMatrix 1 (-X)
  val_inv := by rw [dualNumberMatrix_mul]; simpa using dualNumberMatrix_one (k := k) (n := n)
  inv_val := by rw [dualNumberMatrix_mul]; simpa using dualNumberMatrix_one (k := k) (n := n)

/-- The constructed unit reduces exactly to the identity. -/
theorem dualNumberStrictFrame_fst (X : Matrix n n k) (i j : n) :
    ((dualNumberStrictFrame X).val i j).fst = (1 : Matrix n n k) i j := rfl

/-- Every dual-number frame reducing to the identity has this form. -/
theorem dualNumberStrictFrame_exists (U : GL n (TrivSqZeroExt k k))
    (hU : ∀ i j, (U.val i j).fst = (1 : Matrix n n k) i j) :
    ∃ X : Matrix n n k, U = dualNumberStrictFrame X := by
  refine ⟨fun i j ↦ (U.val i j).snd, ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact TrivSqZeroExt.ext (hU i j) rfl

/-- Conjugation by this strict frame computes the actual changed derivative. -/
theorem dualNumberStrictFrame_conj (X A D : Matrix n n k) :
    (dualNumberStrictFrame X).val * dualNumberMatrix A D * (dualNumberStrictFrame X)⁻¹.val =
      dualNumberMatrix A (D + X * A - A * X) := by
  change dualNumberMatrix 1 X * dualNumberMatrix A D * dualNumberMatrix 1 (-X) = _
  rw [dualNumberMatrix_mul, dualNumberMatrix_mul]
  simp [sub_eq_add_neg, add_comm]

variable {G : Type*} [Group G] (r : G →* GL n k) (D : G → Matrix n n k)

/-- Normalizing the first-order part of actual conjugation gives precisely a coboundary change. -/
theorem dualNumberStrictFrame_coboundary (X : Matrix n n k) :
    normalizedMatrixDerivative r (fun g i j ↦
      ((dualNumberStrictFrame X).val * dualNumberMatrix (r g).val (D g) *
        (dualNumberStrictFrame X)⁻¹.val) i j |>.snd) =
      changeSplitting (normalizedMatrixDerivative r D) (-X) := by
  simp only [dualNumberStrictFrame_conj]
  exact normalizedMatrixDerivative_frame r D X

/-- Strict derivative changes and adjoint coboundaries agree in both directions. -/
theorem matrixDerivative_strict_iff (E : G → Matrix n n k) :
    (∃ X : Matrix n n k, E = fun g ↦ D g + X * (r g).val - (r g).val * X) ↔
      SplittingEquivalent (normalizedMatrixDerivative r D) (normalizedMatrixDerivative r E) := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨-X, normalizedMatrixDerivative_frame r D X⟩
  · rintro ⟨a, ha⟩
    refine ⟨(show Matrix n n k from -a), ?_⟩
    funext g
    apply (Units.mul_left_inj (r g)⁻¹).mp
    have he := congrFun ha g
    have hf := congrFun (normalizedMatrixDerivative_frame r D
      (show Matrix n n k from -a)) g
    exact he.trans (by simpa only [normalizedMatrixDerivative, neg_neg] using hf.symm)

end Deformation
