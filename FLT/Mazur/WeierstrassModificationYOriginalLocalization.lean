/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYFractionMap
public import FLT.Mazur.WeierstrassModificationYRegular

/-!
# Embedding the y-direction chart in the original vertical open

The original fractions s/y and x/y embed the actual y-direction algebra into
the original cubic localized at y. Injectivity uses proved regularity of the
retained original vertical variable, over a domain with nonzero scale.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The principal open obtained by inverting the original vertical coordinate. -/
abbrev OriginalVerticalOpen :=
  Localization.Away (WeierstrassIntegralChart.coord W 2 1)

/-- The inverse relation for the original vertical coordinate. -/
theorem originalVerticalOpen_inverse :
    algebraMap (WeierstrassIntegralChart.Coordinate W 2) (OriginalVerticalOpen W)
      (WeierstrassIntegralChart.coord W 2 1) *
        IsLocalization.Away.invSelf (WeierstrassIntegralChart.coord W 2 1) = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- The y-direction chart maps to actual original fractions. -/
def toOriginalVerticalOpen : Coordinate W s b3 b4 b6 →ₐ[R] OriginalVerticalOpen W :=
  fractionMap W s b3 b4 b6 h3 h4 h6 (IsScalarTower.toAlgHom R _ _)
    (IsLocalization.Away.invSelf
      (WeierstrassIntegralChart.coord W 2 1))
    (originalVerticalOpen_inverse W)

/-- This embedding respects the original contraction on every original function. -/
theorem toOriginalVerticalOpen_fromOriginal :
    (toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6) = IsScalarTower.toAlgHom R _ _ :=
  fractionMap_fromOriginal W s b3 b4 b6 h3 h4 h6 _ _ _

/-- The actual fraction map is injective over a domain with nonzero scale. -/
theorem toOriginalVerticalOpen_injective [IsDomain R] [IsBezout R] (hs : s ≠ 0) :
    Function.Injective (toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6) := by
  let B := Coordinate W s b3 b4 b6
  let L := Localization.Away (coord W s b3 b4 b6 2)
  let g : B →ₐ[R] L := IsScalarTower.toAlgHom R B L
  have hu : IsUnit (g (coord W s b3 b4 b6 2)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let back : OriginalVerticalOpen W →ₐ[R] L :=
    IsLocalization.Away.liftAlgHom (WeierstrassIntegralChart.coord W 2 1)
      (f := g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) (by
        rw [AlgHom.comp_apply, fromOriginal_y]
        exact hu)
  have hc : back.comp (toOriginalVerticalOpen W s b3 b4 b6 h3 h4 h6) = g := by
    symm
    apply lift_unique W s b3 b4 b6 h3 h4 h6 g _ hu.isRegular
    symm
    rw [AlgHom.comp_assoc, toOriginalVerticalOpen_fromOriginal]
    apply AlgHom.ext
    intro a
    change back (algebraMap (WeierstrassIntegralChart.Coordinate W 2)
      (OriginalVerticalOpen W) a) = g (fromOriginal W s b3 b4 b6 h3 h4 h6 a)
    simp only [back, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply]; rfl
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_isRegular
      (Submonoid.powers (coord W s b3 b4 b6 2))).mpr
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := ha
    exact (vertical_regular W s b3 b4 b6 h3 h4 h6 hs).pow n
  intro a b hab
  apply hg
  have he := congrArg (fun k : B →ₐ[R] L => k a) hc
  have he' := congrArg (fun k : B →ₐ[R] L => k b) hc
  exact he.symm.trans ((congrArg back hab).trans he')

end FLT.Mazur.WeierstrassModificationY
