/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFractionMap
public import FLT.Mazur.WeierstrassModificationXFlat

/-!
# Embedding the x-direction chart in the original horizontal open

The original fractions s/x and y/x embed the actual x-direction algebra into
the original cubic localized at x. Injectivity uses proved regularity of the
retained original horizontal variable, over a domain with nonzero scale.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The principal open obtained by inverting the original horizontal coordinate. -/
abbrev OriginalHorizontalOpen :=
  Localization.Away (WeierstrassIntegralChart.coord W 2 0)

/-- The inverse relation for the original horizontal coordinate. -/
theorem originalHorizontalOpen_inverse :
    algebraMap (WeierstrassIntegralChart.Coordinate W 2) (OriginalHorizontalOpen W)
      (WeierstrassIntegralChart.coord W 2 0) *
        IsLocalization.Away.invSelf (WeierstrassIntegralChart.coord W 2 0) = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- The x-direction chart maps to actual original fractions. -/
def toOriginalHorizontalOpen : Coordinate W s b3 b4 b6 →ₐ[R] OriginalHorizontalOpen W :=
  fractionMap W s b3 b4 b6 h3 h4 h6 (IsScalarTower.toAlgHom R _ _)
    (IsLocalization.Away.invSelf
      (WeierstrassIntegralChart.coord W 2 0))
    (originalHorizontalOpen_inverse W)

/-- This embedding respects the original contraction on every original function. -/
theorem toOriginalHorizontalOpen_fromOriginal :
    (toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6) = IsScalarTower.toAlgHom R _ _ :=
  fractionMap_fromOriginal W s b3 b4 b6 h3 h4 h6 _ _ _

/-- The actual fraction map is injective over a domain with nonzero scale. -/
theorem toOriginalHorizontalOpen_injective [IsDomain R] (hs : s ≠ 0) :
    Function.Injective (toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6) := by
  let B := Coordinate W s b3 b4 b6
  let L := Localization.Away (x W s b3 b4 b6)
  let g : B →ₐ[R] L := IsScalarTower.toAlgHom R B L
  have hu : IsUnit (g (x W s b3 b4 b6)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let back : OriginalHorizontalOpen W →ₐ[R] L :=
    IsLocalization.Away.liftAlgHom (WeierstrassIntegralChart.coord W 2 0)
      (f := g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) (by
        rw [AlgHom.comp_apply, fromOriginal_x]
        exact hu)
  have hc : back.comp (toOriginalHorizontalOpen W s b3 b4 b6 h3 h4 h6) = g := by
    symm
    apply lift_unique W s b3 b4 b6 h3 h4 h6 g _ hu.isRegular
    symm
    rw [AlgHom.comp_assoc, toOriginalHorizontalOpen_fromOriginal]
    apply AlgHom.ext
    intro a
    change back (algebraMap (WeierstrassIntegralChart.Coordinate W 2)
      (OriginalHorizontalOpen W) a) = g (fromOriginal W s b3 b4 b6 h3 h4 h6 a)
    simp only [back, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply]; rfl
  have hg : Function.Injective g := by
    apply (IsLocalization.injective_iff_isRegular
      (Submonoid.powers (x W s b3 b4 b6))).mpr
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := ha
    exact (x_regular W s b3 b4 b6 hs).pow n
  intro a b hab
  apply hg
  have he := congrArg (fun k : B →ₐ[R] L => k a) hc
  have he' := congrArg (fun k : B →ₐ[R] L => k b) hc
  exact he.symm.trans ((congrArg back hab).trans he')

end FLT.Mazur.WeierstrassModificationX
