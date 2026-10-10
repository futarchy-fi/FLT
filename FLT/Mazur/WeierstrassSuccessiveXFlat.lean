/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMonicComparison
public import FLT.Mazur.WeierstrassSuccessiveXLocalization
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness of the actual x-direction equation algebra

The chart embeds into the divided principal-open algebra. That algebra is
flat over the coefficient ring, so the x chart is torsion-free over a domain
with nonzero step parameter. Over a Bezout domain, in particular a discrete valuation
ring, this proves flatness. The step parameter and retained horizontal coordinate are
also non-zero-divisors, as required for saturation comparisons.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassSuccessiveX

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The actual divided principal-open algebra is flat over the original base. -/
instance dividedOpen_flat : Module.Flat R (DividedOpen W s π b3 b4 b6) :=
  Module.Flat.trans R (WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6)
    (DividedOpen W s π b3 b4 b6)

/-- The actual coordinate map from the x chart to the divided principal-open algebra. -/
def toDividedLocalization : Coordinate W s π b3 b4 b6 →ₐ[R] DividedOpen W s π b3 b4 b6 :=
  (overlapEquiv W s π b3 b4 b6).symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ _)

variable [IsDomain R]

/-- Inverting the incidence ratio loses no actual chart functions. -/
theorem xOpen_algebraMap_injective (hπ : π ≠ 0) :
    Function.Injective (algebraMap (Coordinate W s π b3 b4 b6)
      (XOpen W s π b3 b4 b6)) := by
  apply (IsLocalization.injective_iff_isRegular
    (Submonoid.powers (coord W s π b3 b4 b6 0))).mpr
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := ha
  exact (t_regular W s π b3 b4 b6 hπ).pow n

/-- The coordinate map is injective whenever the step parameter is nonzero. -/
theorem toDividedLocalization_injective (hπ : π ≠ 0) :
    Function.Injective (toDividedLocalization W s π b3 b4 b6) :=
  (overlapEquiv W s π b3 b4 b6).symm.injective.comp
    (xOpen_algebraMap_injective W s π b3 b4 b6 hπ)

/-- The actual x-direction coordinate algebra is torsion-free over its original domain. -/
theorem coordinate_torsionFree (hπ : π ≠ 0) :
    Module.IsTorsionFree R (Coordinate W s π b3 b4 b6) :=
  (toDividedLocalization_injective W s π b3 b4 b6 hπ).moduleIsTorsionFree
    (toDividedLocalization W s π b3 b4 b6)
    (fun r z => map_smul (toDividedLocalization W s π b3 b4 b6) r z)

/-- Over a Bezout domain, the actual equation chart is flat. -/
theorem coordinate_flat_of_parameter_ne_zero [IsBezout R] (hπ : π ≠ 0) :
    Module.Flat R (Coordinate W s π b3 b4 b6) := by
  let _ := coordinate_torsionFree W s π b3 b4 b6 hπ
  exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

/-- Nonzero base elements remain regular in the actual x-direction algebra. -/
theorem base_regular (hπ : π ≠ 0) {a : R} (ha : a ≠ 0) :
    IsRegular (algebraMap R (Coordinate W s π b3 b4 b6) a) := by
  let f := toDividedLocalization W s π b3 b4 b6
  have hf := toDividedLocalization_injective W s π b3 b4 b6 hπ
  have hr : IsRegular (algebraMap R (DividedOpen W s π b3 b4 b6) a) :=
    WeierstrassIntegralChart.flatRingHom_isRegular _
      (RingHom.flat_algebraMap_iff.mpr inferInstance) (IsRegular.of_ne_zero ha)
  refine ⟨?_, ?_⟩
  · intro x y h
    apply hf
    apply hr.left
    simpa only [map_mul, AlgHom.commutes] using congrArg f h
  · intro x y h
    apply hf
    apply hr.right
    simpa only [map_mul, AlgHom.commutes] using congrArg f h

/-- The original horizontal coordinate has no torsion in this equation chart. -/
theorem u_regular (hπ : π ≠ 0) : IsRegular (coord W s π b3 b4 b6 2) := by
  have h := base_regular W s π b3 b4 b6 hπ hπ
  rw [← incidence] at h
  exact h.of_mul_right

/-- Inverting the original horizontal coordinate loses no functions of this chart. -/
theorem horizontal_algebraMap_injective (hπ : π ≠ 0) :
    Function.Injective (algebraMap (Coordinate W s π b3 b4 b6)
      (Localization.Away (coord W s π b3 b4 b6 2))) := by
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (coord W s π b3 b4 b6 2))).mpr
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := ha
  exact (u_regular W s π b3 b4 b6 hπ).pow n

end FLT.Mazur.WeierstrassSuccessiveX
