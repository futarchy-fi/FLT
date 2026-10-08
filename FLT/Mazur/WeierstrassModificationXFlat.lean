/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXIncidenceRegular
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness of the actual x-direction equation algebra

The chart embeds into the divided principal-open algebra. That algebra is
flat over the coefficient ring, so the x chart is torsion-free over a domain
with nonzero scale. Over a Bezout domain, in particular a discrete valuation
ring, this proves flatness. The scale and original horizontal coordinate are
also non-zero-divisors, as required for saturation comparisons.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The actual divided principal-open algebra is flat over the original base. -/
instance dividedOpen_flat : Module.Flat R (DividedOpen W s b3 b4 b6) :=
  Module.Flat.trans R (WeierstrassDilatation.Coordinate W s b3 b4 b6)
    (DividedOpen W s b3 b4 b6)

/-- The actual coordinate map from the x chart to the divided principal-open algebra. -/
def toDividedLocalization : Coordinate W s b3 b4 b6 →ₐ[R] DividedOpen W s b3 b4 b6 :=
  (overlapEquiv W s b3 b4 b6).symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ _)

variable [IsDomain R]

/-- The coordinate map is injective whenever the original scale is nonzero. -/
theorem toDividedLocalization_injective (hs : s ≠ 0) :
    Function.Injective (toDividedLocalization W s b3 b4 b6) :=
  (overlapEquiv W s b3 b4 b6).symm.injective.comp
    (xOpen_algebraMap_injective W s b3 b4 b6 hs)

/-- The actual x-direction coordinate algebra is torsion-free over its original domain. -/
theorem coordinate_torsionFree (hs : s ≠ 0) :
    Module.IsTorsionFree R (Coordinate W s b3 b4 b6) :=
  (toDividedLocalization_injective W s b3 b4 b6 hs).moduleIsTorsionFree
    (toDividedLocalization W s b3 b4 b6)
    (fun r z => map_smul (toDividedLocalization W s b3 b4 b6) r z)

/-- Over a Bezout domain, the actual equation chart is flat. -/
theorem coordinate_flat_of_scale_ne_zero [IsBezout R] (hs : s ≠ 0) :
    Module.Flat R (Coordinate W s b3 b4 b6) := by
  let _ := coordinate_torsionFree W s b3 b4 b6 hs
  exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

/-- Nonzero base elements remain regular in the actual x-direction algebra. -/
theorem base_regular (hs : s ≠ 0) {a : R} (ha : a ≠ 0) :
    IsRegular (algebraMap R (Coordinate W s b3 b4 b6) a) := by
  let _ := coordinate_torsionFree W s b3 b4 b6 hs
  have hm := (IsRegular.of_ne_zero ha).isSMulRegular (M := Coordinate W s b3 b4 b6)
  have hl : IsLeftRegular (algebraMap R (Coordinate W s b3 b4 b6) a) := by
    simpa only [IsLeftRegular, IsSMulRegular, Algebra.smul_def] using hm
  exact ⟨hl, fun x y h => hl (by simpa only [mul_comm] using h)⟩

/-- The original horizontal coordinate has no torsion in this equation chart. -/
theorem x_regular (hs : s ≠ 0) : IsRegular (x W s b3 b4 b6) := by
  have h := base_regular W s b3 b4 b6 hs hs
  rw [← incidence] at h
  exact h.of_mul_right

/-- Inverting the original horizontal coordinate loses no functions of this chart. -/
theorem horizontal_algebraMap_injective (hs : s ≠ 0) :
    Function.Injective (algebraMap (Coordinate W s b3 b4 b6)
      (Localization.Away (x W s b3 b4 b6))) := by
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (x W s b3 b4 b6))).mpr
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := ha
  exact (x_regular W s b3 b4 b6 hs).pow n

end FLT.Mazur.WeierstrassModificationX
