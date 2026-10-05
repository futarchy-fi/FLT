/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCoefficientAffineSheaf

/-!
# Finite coefficient modules on the glued affine charts

Surjectivity of the actual relative quotient and the coefficient chart
isomorphism imply surjectivity of the glued quotient on each affine open.
Thus the actual glued relative module is cyclic on those opens. This does
not require, or assert, an isomorphism for the relative tensor chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The glued quotient is surjective on sections of every actual affine chart. -/
lemma relativeSheafQuotient_surjective (U : X.affineOpens) :
    Function.Surjective ((relativeSheafQuotient J f).hom.app (.op U.1)) := by
  intro s
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((coefficientChartIso J f U).hom)).surjective s
  obtain ⟨r, rfl⟩ := relativeAffineQuotient_surjective J f (.op U) t
  refine ⟨(affineRingSheafificationUnit (relativeAffinePresheaf J f)).app (.op U) r, ?_⟩
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (relativeSheafQuotient_chart J f) (.op U)) r).symm

/-- The original quotient gives a finite ring map on glued affine sections. -/
lemma relativeSheafQuotient_finite (U : X.affineOpens) :
    ((relativeSheafQuotient J f).hom.app (.op U.1)).hom.Finite :=
  RingHom.Finite.of_surjective _ (relativeSheafQuotient_surjective J f U)

/-- The quotient on sections is linear for the actual relative sheaf action. -/
def relativeSheafQuotientLinear (U : X.Opensᵒᵖ) :
    (relativeScalarSheaf J f).obj.obj U →ₗ[(relativeScalarSheaf J f).obj.obj U]
      (relativeCoefficientModuleSheaf J f).val.obj U where
  toFun r := (relativeSheafQuotient J f).hom.app U r
  map_add' r s := map_add _ r s
  map_smul' r s := by
    change (relativeSheafQuotient J f).hom.app U (r * s) =
      (relativeSheafQuotient J f).hom.app U r * (relativeSheafQuotient J f).hom.app U s
    exact map_mul _ r s

/-- Finiteness now holds for the actual glued module on each affine chart. -/
lemma relativeCoefficientModuleSheaf_finite (U : X.affineOpens) :
    Module.Finite ((relativeScalarSheaf J f).obj.obj (.op U.1))
      ((relativeCoefficientModuleSheaf J f).val.obj (.op U.1)) :=
  Module.Finite.of_surjective (relativeSheafQuotientLinear J f (.op U.1))
    (relativeSheafQuotient_surjective J f U)

/-- The constant unit generates the glued coefficient module on every affine open. -/
lemma relativeCoefficientModuleSheaf_cyclic (U : X.affineOpens)
    (s : (relativeCoefficientModuleSheaf J f).val.obj (.op U.1)) :
    ∃ r : (relativeScalarSheaf J f).obj.obj (.op U.1),
      r • (relativeCoefficientSectionEquiv J f (.op U.1)).symm 1 = s := by
  obtain ⟨r, hr⟩ := relativeSheafQuotient_surjective J f U s
  refine ⟨r, ?_⟩
  change (relativeSheafQuotient J f).hom.app (.op U.1) r * 1 = s
  exact (mul_one _).trans hr

end FLT.Mazur.IdealAdicGradedPullback
