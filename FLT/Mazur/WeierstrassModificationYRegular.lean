/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationFlat

/-!
# Regularity of the original vertical coordinate

Flatness of the actual y-direction chart preserves nonzero base elements.
The relation r*z=s then makes both r and the original vertical z regular.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6

/-- Nonzero elements of the original base remain regular on the actual y chart. -/
theorem base_regular (hs : s ≠ 0) {a : R} (ha : a ≠ 0) :
    IsRegular (algebraMap R (Coordinate W s b3 b4 b6) a) := by
  let _ := WeierstrassModificationX.yCoordinate_flat W s b3 b4 b6 h3 h4 h6 hs
  exact WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) (IsRegular.of_ne_zero ha)

/-- The original vertical coordinate is a non-zero-divisor in the y-direction algebra. -/
theorem vertical_regular (hs : s ≠ 0) : IsRegular (coord W s b3 b4 b6 2) := by
  have h := base_regular W s b3 b4 b6 h3 h4 h6 hs hs
  rw [← incidence] at h
  exact h.of_mul_right

/-- The scale ratio is also regular in the y-direction algebra. -/
theorem scaleRatio_regular (hs : s ≠ 0) : IsRegular (coord W s b3 b4 b6 0) := by
  have h := base_regular W s b3 b4 b6 h3 h4 h6 hs hs
  rw [← incidence] at h
  exact h.of_mul_left

/-- Localizing at the original vertical coordinate loses no chart functions. -/
theorem vertical_algebraMap_injective (hs : s ≠ 0) :
    Function.Injective (algebraMap (Coordinate W s b3 b4 b6)
      (Localization.Away (coord W s b3 b4 b6 2))) := by
  apply (IsLocalization.injective_iff_isRegular
    (Submonoid.powers (coord W s b3 b4 b6 2))).mpr
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := ha
  exact (vertical_regular W s b3 b4 b6 h3 h4 h6 hs).pow n

end FLT.Mazur.WeierstrassModificationY
