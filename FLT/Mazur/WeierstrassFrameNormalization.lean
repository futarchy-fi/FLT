/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeFrame
public import Mathlib.Tactic.Group

/-!
# Canonical normalization of a unit-separated Weierstrass frame

The horizontal and vertical separations determine an admissible change of
variables over the original ring. No field, reducedness, or division by
three is used. The chosen frame becomes (0,0), (0,-d), and (-d,0).
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassFrameNormalization

variable {R : Type*} [CommRing R]

/-- The scale is the ratio of the vertical and horizontal unit differences. -/
def scale (h v : Rˣ) : Rˣ := v * h⁻¹

/-- Translation and shear retain the original first and third frame points. -/
def change (x y w : R) (h v : Rˣ) : VariableChange R :=
  ⟨scale h v, x, (y - w) * ↑h⁻¹, y⟩

/-- The common normalized separation is still a unit. -/
def separation (h v : Rˣ) : Rˣ := h * (scale h v)⁻¹ ^ 2

/-- Vertical and horizontal normalized differences agree by the chosen scale. -/
theorem scale_separation (h v : Rˣ) :
    scale h v * separation h v = v * (scale h v)⁻¹ ^ 2 := by
  dsimp [scale, separation]
  group

/-- Undoing normalization on the horizontal separation gives the original unit. -/
theorem square_separation (h v : Rˣ) :
    scale h v ^ 2 * separation h v = h := by
  dsimp only [separation]
  rw [mul_left_comm, ← mul_pow, mul_inv_cancel, one_pow, mul_one]

/-- Undoing normalization on the vertical separation gives the original unit. -/
theorem cube_separation (h v : Rˣ) :
    scale h v ^ 3 * separation h v = v := by
  calc
    _ = scale h v * (scale h v ^ 2 * separation h v) := by group
    _ = v := by rw [square_separation]; simp [scale]

/-- The first normalized point maps to the original first point. -/
theorem change_first (x y w : R) (h v : Rˣ) :
    (change x y w h v).u.val ^ 2 * 0 + (change x y w h v).r = x ∧
      (change x y w h v).u.val ^ 3 * 0 +
        (change x y w h v).u.val ^ 2 * (change x y w h v).s * 0 +
          (change x y w h v).t = y := by
  simp only [change, mul_zero, zero_add, and_self]

/-- The inverse member of the vertical pair has normalized ordinate minus the separation. -/
theorem change_inverse (x y y' w : R) (h v : Rˣ) (hv : (v : R) = y - y') :
    (change x y w h v).u.val ^ 3 * -(separation h v : R) +
      (change x y w h v).u.val ^ 2 * (change x y w h v).s * 0 +
        (change x y w h v).t = y' := by
  have hc := congrArg (fun u : Rˣ ↦ (u : R)) (cube_separation h v)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hc
  dsimp only [change]
  rw [mul_zero, add_zero, mul_neg, hc, hv]
  ring

/-- The horizontally separated point has normalized ordinate zero and abscissa minus d. -/
theorem change_third (x y z w : R) (h v : Rˣ) (hh : (h : R) = x - z) :
    (change x y w h v).u.val ^ 2 * -(separation h v : R) +
        (change x y w h v).r = z ∧
      (change x y w h v).u.val ^ 3 * 0 +
        (change x y w h v).u.val ^ 2 * (change x y w h v).s *
          -(separation h v : R) + (change x y w h v).t = w := by
  have hc := congrArg (fun u : Rˣ ↦ (u : R)) (square_separation h v)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hc
  dsimp only [change]
  constructor
  · rw [mul_neg, hc, hh]
    ring
  · rw [mul_zero, zero_add]
    calc
      _ = -(y - w) * ((scale h v : R) ^ 2 * (separation h v : R)) * ↑h⁻¹ + y := by
        ring
      _ = w := by rw [hc, mul_assoc, h.mul_inv]; ring

end FLT.Mazur.WeierstrassFrameNormalization
