/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineDenominator

/-!
# Regular Vélu coordinates on the explicit denominator open

Recover the original uncompleted y-coordinate inside the localization. The
injective generic comparison proves the target equation in this actual ring.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The original uncompleted target y-coordinate on the denominator open. -/
def veluAffineY : VeluAffineLocalization E G :=
  (veluAffineSlope E G *
      (2 * algebraMap _ _ (coord E 2 1) +
        algebraMap K _ E.a₁ * algebraMap _ _ (coord E 2 0) + algebraMap K _ E.a₃) -
    algebraMap K _ (curve E G).a₁ * veluAffineX E G - algebraMap K _ (curve E G).a₃) *
      algebraMap K _ (2⁻¹ : K)

/-- Coefficient functions in the localization retain their original affine values. -/
@[simp] theorem veluAffineLocalizationHom_algebraMap (a : Coordinate E 2) :
    veluAffineLocalizationHom E G (algebraMap _ (VeluAffineLocalization E G) a) =
      sourceGenericChart E a :=
  sourceLocalizationHom_algebraMap E _ _ a

/-- The regular y-coordinate agrees exactly with the original generic formula. -/
theorem veluAffineY_generic :
    veluAffineLocalizationHom E G (veluAffineY E G) =
      liftY E (curve E G) (xFunction E G) (slopeFunction E G) := by
  simp only [veluAffineY, map_mul, map_sub, map_add, map_ofNat, AlgHom.commutes,
    veluAffineSlope_generic, veluAffineX_generic, veluAffineLocalizationHom_algebraMap,
    sourceGenericChart_x, sourceGenericChart_y]
  rw [map_inv₀, map_ofNat, ← div_eq_mul_inv]
  apply (div_eq_iff (by norm_num : (2 : FunctionField E) ≠ 0)).mpr
  apply QuadraticAlgebra.ext
  all_goals simp [liftX, liftY] <;> ring_nf <;> simp only [or_true]

/-- The actual localized coordinates satisfy the actual target affine equation. -/
theorem veluAffine_equation (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    ((curve E G).map (algebraMap K (VeluAffineLocalization E G))).toAffine.Equation
      (veluAffineX E G) (veluAffineY E G) := by
  have h := velu_lift_equation E G hodd
  rw [← veluAffineX_generic E G, ← veluAffineY_generic E G] at h
  apply (Affine.map_equation _ (veluAffineLocalizationHom_injective E G) _ _).mp
  change ((curve E G).map
    ((veluAffineLocalizationHom E G).toRingHom.comp
      (algebraMap K (VeluAffineLocalization E G)))).toAffine.Equation _ _
  have hc : (veluAffineLocalizationHom E G).toRingHom.comp
      (algebraMap K (VeluAffineLocalization E G)) = algebraMap K (FunctionField E) := by
    apply RingHom.ext
    intro c
    exact (veluAffineLocalizationHom E G).commutes c
  rw [hc]
  exact h

end WeierstrassCurve.Velu
