/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationFractionMap
public import FLT.Mazur.WeierstrassDilatationLifting

/-!
# Embedding the divided chart into the original principal open

The divided coordinates map to the actual fractions x/s and y/s in the
original cubic algebra localized at s. Regularity of the scale proves this
map injective, retaining the original algebra rather than an abstract fiber.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The principal open in the original affine cubic obtained by inverting its scale. -/
abbrev OriginalScaleOpen :=
  Localization.Away (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s)

/-- The inverse of the original base scale in the original principal open. -/
theorem originalScaleOpen_inverse :
    algebraMap R (OriginalScaleOpen W s) s *
      IsLocalization.Away.invSelf
        (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s) = 1 := by
  rw [IsScalarTower.algebraMap_apply R (WeierstrassIntegralChart.Coordinate W 2)
    (OriginalScaleOpen W s)]
  exact IsLocalization.Away.mul_invSelf _

/-- The divided chart maps to actual original fractions. -/
def toOriginalScaleOpen : Coordinate W s b3 b4 b6 →ₐ[R] OriginalScaleOpen W s :=
  fractionMap W s b3 b4 b6 h3 h4 h6 (IsScalarTower.toAlgHom R _ _)
    (IsLocalization.Away.invSelf
      (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s))
    (originalScaleOpen_inverse W s)

/-- This embedding respects the original contraction on every original function. -/
theorem toOriginalScaleOpen_fromOriginal :
    (toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6) = IsScalarTower.toAlgHom R _ _ :=
  fractionMap_fromOriginal W s b3 b4 b6 h3 h4 h6 _ _ _

/-- The actual fraction map is injective for any regular scale. -/
theorem toOriginalScaleOpen_injective (hs : IsRegular s) :
    Function.Injective (toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6) := by
  let B := Coordinate W s b3 b4 b6
  let L := Localization.Away (algebraMap R B s)
  let g : B →ₐ[R] L := IsScalarTower.toAlgHom R B L
  have hu : IsUnit (algebraMap R L s) := by
    rw [IsScalarTower.algebraMap_apply R B L]
    exact IsLocalization.Away.algebraMap_isUnit _
  let back : OriginalScaleOpen W s →ₐ[R] L :=
    IsLocalization.Away.liftAlgHom (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s)
      (f := g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) (by
        rw [AlgHom.commutes]
        exact hu)
  have hc : back.comp (toOriginalScaleOpen W s b3 b4 b6 h3 h4 h6) = g := by
    apply lift_unique W s b3 b4 b6 h3 h4 h6 hu.isRegular
    rw [AlgHom.comp_assoc, toOriginalScaleOpen_fromOriginal]
    apply AlgHom.ext
    intro a
    change back (algebraMap (WeierstrassIntegralChart.Coordinate W 2)
      (OriginalScaleOpen W s) a) = g (fromOriginal W s b3 b4 b6 h3 h4 h6 a)
    simp only [back, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply]; rfl
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_isRegular
      (Submonoid.powers (algebraMap R B s))).mpr
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := ha
    exact (scale_regular W s b3 b4 b6 hs).pow n
  intro a b hab
  apply hg
  have he := congrArg (fun k : B →ₐ[R] L => k a) hc
  have he' := congrArg (fun k : B →ₐ[R] L => k b) hc
  exact he.symm.trans ((congrArg back hab).trans he')

end FLT.Mazur.WeierstrassDilatation
