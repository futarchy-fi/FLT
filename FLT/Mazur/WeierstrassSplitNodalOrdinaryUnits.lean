/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalSlopeRelations

/-!
# Ordinary nodal output units over arbitrary rings

Polynomial identities clear the slope denominator without division. For smooth
affine inputs they force the ordinary output Y coordinate to be a unit, even
over rings with nilpotents.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {S : Type*} [CommRing S] {a r s l : S}

/-- Clearing the ordinary slope denominator in the output X coordinate. -/
theorem splitNodalOrdinary_x_denominator
    (hl : l * (r + s + a) = r ^ 2 + r * s + s ^ 2 + a * (r + s)) :
    (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve S).toAffine.addX
        (r * (r + a)) (s * (s + a)) l * (r + s + a) ^ 2 =
      r * s * (r + a) * (s + a) := by
  dsimp [Affine.addX, toAffine]
  linear_combination
    (a ^ 2 + a * l + 2 * a * r + 2 * a * s + l * r + l * s +
      r ^ 2 + r * s + s ^ 2) * hl

/-- Clearing the ordinary slope denominator in the output Y coordinate. -/
theorem splitNodalOrdinary_y_denominator
    (hl : l * (r + s + a) = r ^ 2 + r * s + s ^ 2 + a * (r + s)) :
    (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve S).toAffine.addY
        (r * (r + a)) (s * (s + a)) (r ^ 2 * (r + a)) l * (r + s + a) ^ 3 =
      r ^ 2 * s ^ 2 * (r + a) * (s + a) := by
  have hx := splitNodalOrdinary_x_denominator hl
  dsimp [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, toAffine] at hx ⊢
  linear_combination -(l + a) * (r + s + a) * hx +
    (r * (r + a) * (r + s + a) ^ 2 - r * s * (r + a) * (s + a)) * hl

/-- Smooth affine nodal inputs have a unit ordinary output Y coordinate. -/
theorem splitNodalOrdinary_y_isUnit
    (hl : l * (r + s + a) = r ^ 2 + r * s + s ^ 2 + a * (r + s))
    (hr : IsUnit r) (hs : IsUnit s) (hra : IsUnit (r + a)) (hsa : IsUnit (s + a)) :
    IsUnit ((⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve S).toAffine.addY
      (r * (r + a)) (s * (s + a)) (r ^ 2 * (r + a)) l) := by
  have hu := ((hr.pow 2).mul (hs.pow 2)).mul hra |>.mul hsa
  exact isUnit_of_mul_isUnit_left ((splitNodalOrdinary_y_denominator hl).symm ▸ hu)

end FLT.Mazur.WeierstrassIntegralChart
