/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalSubstitution

/-!
# Identity restrictions and linear terms of the elliptic addition series

The integral series has linear part X + Y. Its axis restrictions and symmetry
are proved as actual substitution identities. Associativity is still required
before this series can be packaged as a formal group law.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open MvPowerSeries Finsupp

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Restricting to the first axis is the identity series. -/
theorem additionSeries_X_zero :
    (additionSeries W).subst ![PowerSeries.X, 0] = (PowerSeries.X : PowerSeries R) := by
  rw [additionSeries_subst W (by simp [PowerSeries.X]) (by simp),
    add_zero W (by simp [PowerSeries.X])]

/-- Restricting to the second axis is the identity series. -/
theorem additionSeries_zero_X :
    (additionSeries W).subst ![0, PowerSeries.X] = (PowerSeries.X : PowerSeries R) := by
  rw [additionSeries_subst W (by simp) (by simp [PowerSeries.X]),
    zero_add W (by simp [PowerSeries.X])]

/-- Swapping the variables preserves the integral addition series. -/
theorem additionSeries_swap :
    (additionSeries W).subst ![X 1, X 0] = additionSeries W := by
  rw [additionSeries_subst W (by simp) (by simp), add_comm W (by simp) (by simp)]
  rfl

/-- The linear coefficient on the first axis extracts the X coefficient. -/
theorem coeff_one_first_axis (f : MvPowerSeries (Fin 2) R) :
    PowerSeries.coeff 1 (f.subst ![PowerSeries.X, 0]) = coeff (single 0 1) f := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 0 1)]
  · simp
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · by_cases hd₀ : d 0 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.X_zero

/-- The linear coefficient on the second axis extracts the Y coefficient. -/
theorem coeff_one_second_axis (f : MvPowerSeries (Fin 2) R) :
    PowerSeries.coeff 1 (f.subst ![0, PowerSeries.X]) = coeff (single 1 1) f := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 1 1)]
  · simp
  · intro d hd
    by_cases hd₁ : d 0 = 0
    · by_cases hd₀ : d 1 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.zero_X

/-- The linear X coefficient of the elliptic addition series is one. -/
@[simp] theorem additionSeries_coeff_X : coeff (single 0 1) (additionSeries W) = 1 := by
  rw [← coeff_one_first_axis, additionSeries_X_zero]
  simp

/-- The linear Y coefficient of the elliptic addition series is one. -/
@[simp] theorem additionSeries_coeff_Y : coeff (single 1 1) (additionSeries W) = 1 := by
  rw [← coeff_one_second_axis, additionSeries_zero_X]
  simp

end FLT.Mazur.FormalInfinity
