/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Pi

/-!
# Extension by zero from a residual ring factor

An actual product decomposition constructs the residual extension. Its image
is exactly the coefficients zero on every other branch. Multiplication by
an arbitrary original coefficient is retained, without reducedness assumptions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ResidualProductExtension
variable {B : Type*} [CommRing B] {ι : Type*} {C : Option ι → Type*}
  [∀ i, CommRing (C i)] (e : B ≃+* ∀ i, C i)

/-- The actual residual projection of the original coefficient ring. -/
def projection : B →+* C none := (Pi.evalRingHom C none).comp e.toRingHom

/-- Extend a residual coefficient by zero on all other factors. -/
def extension : C none →+ B where
  toFun c := e.symm (fun i ↦ match i with | none => c | some _ => 0)
  map_zero' := by
    convert map_zero e.symm using 1
    congr 1
    funext i
    cases i <;> rfl
  map_add' a b := by
    rw [← map_add]
    congr 1
    funext i
    cases i <;> simp only [Pi.add_apply, add_zero]

/-- The residual coordinate is preserved exactly. -/
theorem extension_none (c : C none) : e (extension e c) none = c := by
  change e (e.symm _) none = c
  rw [e.apply_symm_apply]

/-- Every nonresidual coordinate of the extension is zero. -/
theorem extension_some (c : C none) (i : ι) : e (extension e c) (some i) = 0 := by
  change e (e.symm _) (some i) = 0
  rw [e.apply_symm_apply]

/-- Restriction has the constructed extension as a right inverse. -/
theorem projection_extension (c : C none) : projection e (extension e c) = c :=
  extension_none e c

/-- Extension loses no residual coefficient. -/
theorem extension_injective : Function.Injective (extension e) :=
  Function.LeftInverse.injective (projection_extension e)

/-- Extension reconstructs every coefficient vanishing on the other branches. -/
theorem extension_projection (b : B) (hb : ∀ i, e b (some i) = 0) :
    extension e (projection e b) = b := by
  apply e.injective
  funext i
  cases i with
  | none => exact extension_none e _
  | some i => exact (extension_some e _ i).trans (hb i).symm

/-- Multiplication by an original coefficient is compatible with extension. -/
theorem mul_extension (b : B) (c : C none) :
    b * extension e c = extension e (projection e b * c) := by
  apply e.injective
  funext i
  rw [map_mul]
  cases i with
  | none => simp only [Pi.mul_apply, extension_none]; rfl
  | some i => simp only [Pi.mul_apply, extension_some, mul_zero]

/-- The extended unit is the idempotent selecting the whole residual component. -/
theorem extension_one_idempotent : IsIdempotentElem (extension e 1) := by
  change extension e 1 * extension e 1 = extension e 1
  rw [mul_extension, projection_extension, one_mul]

/-- The residual-supported coefficients form the principal ideal of that idempotent. -/
theorem supported_iff_mul_idempotent (b : B) :
    (∀ i, e b (some i) = 0) ↔ b * extension e 1 = b := by
  rw [mul_extension, mul_one]
  constructor
  · exact extension_projection e b
  · intro h i
    rw [← h]
    exact extension_some e _ i

end FLT.Mazur.ResidualProductExtension
