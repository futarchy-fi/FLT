/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberUnitComparison

/-!
# Coordinate formulas under transport of the product constant

These generic equalities keep coefficient casts out of residue-field proof
reduction while preserving both tangent generators.
-/

@[expose] public noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.NodalFiber
variable {R : Type*} [CommRing R]

/-- Equal constants identify the actual product algebras. -/
def constantEquiv (c d : R) (h : c = d) : Coordinate c ≃ₐ[R] Coordinate d := by
  rw [h]

/-- Constant transport preserves the first tangent factor. -/
@[simp] theorem constantEquiv_p (c d : R) (h : c = d) :
    constantEquiv c d h (p c) = p d := by
  subst d
  rfl

/-- Constant transport preserves the second tangent factor. -/
@[simp] theorem constantEquiv_q (c d : R) (h : c = d) :
    constantEquiv c d h (q c) = q d := by
  subst d
  rfl

/-- Transport the existing Laurent comparison to an equal specified constant. -/
def unitLaurentCast (u : Rˣ) (c : R) (h : ↑u = c) : Coordinate c ≃ₐ[R] R[T;T⁻¹] := by
  have e := laurentEquiv u
  rw [h] at e
  exact e

/-- The first factor is still the Laurent parameter after transport. -/
@[simp] theorem unitLaurentCast_p (u : Rˣ) (c : R) (h : ↑u = c) :
    unitLaurentCast u c h (p c) = T 1 := by
  subst c
  exact toLaurent_p u

/-- The second factor uses the specified original constant after transport. -/
@[simp] theorem unitLaurentCast_q (u : Rˣ) (c : R) (h : ↑u = c) :
    unitLaurentCast u c h (q c) = C c * T (-1) := by
  subst c
  exact toLaurent_q u

end FLT.Mazur.NodalFiber
