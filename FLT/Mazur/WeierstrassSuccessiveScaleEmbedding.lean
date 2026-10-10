/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveScaleFractions

/-!
# Embedding the deeper divided chart in preceding scale fractions

The fraction substitution is injective for a regular π, regardless of the
old scale s. Flatness of the deeper divided algebra supplies regularity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveScale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "ref" => WeierstrassDilatation.refinement W s π
  (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl

/-- The preceding divided algebra with the new scale inverted. -/
abbrev PreviousScaleOpen := Localization.Away (algebraMap R B π)

/-- The localization inverse inverts the original base parameter. -/
theorem previousScaleOpen_inverse :
    algebraMap R (PreviousScaleOpen W s π b3 b4 b6) π *
      IsLocalization.Away.invSelf (algebraMap R B π) = 1 := by
  rw [IsScalarTower.algebraMap_apply R B (PreviousScaleOpen W s π b3 b4 b6)]
  exact IsLocalization.Away.mul_invSelf _

/-- The actual deeper equation maps to preceding fractions. -/
def toPreviousScaleOpen : D →ₐ[R] PreviousScaleOpen W s π b3 b4 b6 :=
  fractionMap W s π b3 b4 b6 (IsScalarTower.toAlgHom R _ _)
    (IsLocalization.Away.invSelf (algebraMap R B π))
    (previousScaleOpen_inverse W s π b3 b4 b6)

/-- The embedding retains every preceding function under refinement. -/
theorem toPreviousScaleOpen_refinement :
    (toPreviousScaleOpen W s π b3 b4 b6).comp ref = IsScalarTower.toAlgHom R _ _ :=
  fractionMap_refinement W s π b3 b4 b6 _ _ _

/-- Regularity of the new scale survives in the deeper divided algebra. -/
theorem deeper_scale_regular (hπ : IsRegular π) : IsRegular (algebraMap R D π) :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hπ

/-- No deeper chart function is killed by the preceding fraction substitution. -/
theorem toPreviousScaleOpen_injective (hπ : IsRegular π) :
    Function.Injective (toPreviousScaleOpen W s π b3 b4 b6) := by
  let L := Localization.Away (algebraMap R D π)
  let g : D →ₐ[R] L := IsScalarTower.toAlgHom R D L
  have hu : IsUnit (algebraMap R L π) := by
    rw [IsScalarTower.algebraMap_apply R D L]
    exact IsLocalization.Away.algebraMap_isUnit _
  let back : PreviousScaleOpen W s π b3 b4 b6 →ₐ[R] L :=
    IsLocalization.Away.liftAlgHom (algebraMap R B π) (f := g.comp ref) (by
      rw [AlgHom.commutes]
      exact hu)
  have hc : back.comp (toPreviousScaleOpen W s π b3 b4 b6) = g := by
    apply refinement_hom_ext W s π b3 b4 b6 hu.isRegular
    rw [AlgHom.comp_assoc, toPreviousScaleOpen_refinement]
    apply AlgHom.ext
    intro a
    change back (algebraMap B (PreviousScaleOpen W s π b3 b4 b6) a) = g (ref a)
    simp only [back, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply]
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_isRegular
      (Submonoid.powers (algebraMap R D π))).mpr
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := ha
    exact (deeper_scale_regular W s π b3 b4 b6 hπ).pow n
  intro a b hab
  apply hg
  exact (AlgHom.congr_fun hc a).symm.trans
    ((congrArg back hab).trans (AlgHom.congr_fun hc b))

end FLT.Mazur.WeierstrassSuccessiveScale
