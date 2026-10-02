/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The one-gon puncture coordinate transition

On R[t, 1/(t(t-1))], the coordinate change t ↦ t/(t-1) is an involution.
This supplies the overlap coordinate of the chart pinching zero and one;
it does not yet construct the gluing or prove the pinching universal property.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.OneGonTransition

variable (R : Type*) [CommRing R]

/-- Coordinate ring of the affine line with zero and one removed. -/
abbrev puncture := Localization.Away (X * (X - 1) : R[X])

/-- The normalization coordinate, invertible on the puncture. -/
def coordinate : (puncture R)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := puncture R)
    (X * (X - 1) : R[X]) (dvd_mul_right X (X - 1))).unit

/-- The difference from one, also invertible on the puncture. -/
def difference : (puncture R)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := puncture R)
    (X * (X - 1) : R[X]) (dvd_mul_left (X - 1) X)).unit

@[simp]
theorem coordinate_val : (coordinate R : puncture R) = algebraMap R[X] _ X :=
  IsUnit.unit_spec _

@[simp]
theorem difference_val :
    (difference R : puncture R) = (coordinate R : puncture R) - 1 := by
  simp [difference]

/-- The new coordinate t/(t-1). -/
def mobius : (puncture R)ˣ := coordinate R * (difference R)⁻¹

theorem mobius_sub_one :
    (mobius R : puncture R) - 1 = (↑(difference R)⁻¹ : puncture R) := by
  have h := Units.mul_inv (difference R)
  change (difference R : puncture R) * (↑(difference R)⁻¹ : puncture R) = 1 at h
  rw [difference_val] at h
  change (coordinate R : puncture R) * (↑(difference R)⁻¹ : puncture R) - 1 = _
  rw [sub_mul, one_mul, sub_eq_iff_eq_add] at h
  rw [h, add_sub_cancel_left]

/-- Substitution by the new coordinate respects the inverted conductor. -/
theorem eval_conductor_isUnit :
    IsUnit ((aeval (mobius R : puncture R)) (X * (X - 1) : R[X])) := by
  simp only [map_mul, map_sub, map_one, aeval_X, mobius_sub_one]
  exact (mobius R).isUnit.mul ((difference R)⁻¹).isUnit

/-- The coordinate change on the punctured normalization. -/
def transition : puncture R →ₐ[R] puncture R :=
  IsLocalization.Away.liftAlgHom (X * (X - 1) : R[X]) (eval_conductor_isUnit R)

theorem transition_coordinate :
    transition R (coordinate R : puncture R) = (mobius R : puncture R) := by
  simp [transition, IsLocalization.Away.liftAlgHom_apply]

theorem transition_difference :
    transition R (difference R : puncture R) = (↑(difference R)⁻¹ : puncture R) := by
  rw [difference_val, map_sub, map_one, transition_coordinate, mobius_sub_one]

theorem transition_difference_inv :
    transition R (↑(difference R)⁻¹ : puncture R) = (difference R : puncture R) := by
  have h : Units.map (transition R).toMonoidHom (difference R) = (difference R)⁻¹ := by
    apply Units.ext
    exact transition_difference R
  have hh := congrArg (fun a : (puncture R)ˣ ↦ (↑a⁻¹ : puncture R)) h
  simpa using hh

@[simp]
theorem transition_mobius :
    transition R (mobius R : puncture R) = (coordinate R : puncture R) := by
  simp only [mobius, Units.val_mul, map_mul, transition_difference_inv]
  rw [transition_coordinate]
  change ((coordinate R : puncture R) * ↑(difference R)⁻¹) * ↑(difference R) = _
  rw [mul_assoc, Units.inv_mul, mul_one]

/-- Applying the overlap coordinate change twice is the identity. -/
theorem transition_involutive : Function.Involutive (transition R) := by
  have h : (transition R).comp (transition R) = AlgHom.id R (puncture R) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (X * (X - 1) : R[X]))
    ext
    change transition R (transition R (coordinate R : puncture R)) =
      (coordinate R : puncture R)
    rw [transition_coordinate, transition_mobius]
  intro x
  exact congrArg (fun f : puncture R →ₐ[R] puncture R ↦ f x) h

/-- The one-gon overlap transition is an algebra isomorphism. -/
def transitionEquiv : puncture R ≃ₐ[R] puncture R :=
  AlgEquiv.ofAlgHom (transition R) (transition R)
    (AlgHom.ext (transition_involutive R)) (AlgHom.ext (transition_involutive R))

end FLT.Mazur.OneGonTransition
