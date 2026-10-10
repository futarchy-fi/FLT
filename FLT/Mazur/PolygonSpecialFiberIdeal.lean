/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedLineQuotientPresentation
public import FLT.Mazur.PolygonInfinitesimalStageFiber
public import FLT.Mazur.PolygonStageLineQuotient

/-!
# The original closed polygon as the parameter subscheme

The original special-fiber inclusion has exactly the extended parameter
ideal as kernel. The resulting line quotient comparison preserves its unit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve BaseAdicThickening IdealAdicQuotient Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- The original closed coefficient reduction has the parameter ideal as kernel. -/
theorem reduction_ker : RingHom.ker (reduction K m).toRingHom =
    Ideal.span {parameter K m} := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (reduction_eq_zero_iff K m z).trans (exists_congr fun _ ↦ eq_comm)

/-- The coefficient closed-fiber map has the actual principal ideal sheaf as kernel. -/
theorem reductionBase_ker : (reductionBase K m).ker =
    baseIdeal (.of (Ring K m)) (Ideal.span {parameter K m}) := by
  rw [reductionBase, specMap_ker_baseIdeal]
  change baseIdeal (.of (Ring K m)) (RingHom.ker (reduction K m).toRingHom) = _
  rw [reduction_ker]

/-- The original closed polygon is cut out by the actual stage parameter. -/
theorem specialFiberInclusion_ker : (specialFiberInclusion K m n h).ker =
    stageParameterIdeal K m n h := by
  rw [← specialFiberPullbackIso_fst K m n h, Scheme.Hom.ker_comp_of_isIso,
    ker_fst_of_isClosedImmersion, reductionBase_ker]
  rfl

/-- The original polygon identifies with the actual parameter subscheme. -/
def specialFiberIdealIso : PolygonCyclicAtlas.scheme K n h ≅
    (stageParameterIdeal K m n h).subscheme :=
  asIso (specialFiberInclusion K m n h).toImage ≪≫
    subschemeCongr (specialFiberInclusion_ker K m n h)

/-- The identification retains the specified closed polygon inclusion. -/
@[reassoc] theorem specialFiberIdealIso_hom_ι :
    (specialFiberIdealIso K m n h).hom ≫ (stageParameterIdeal K m n h).subschemeι =
      specialFiberInclusion K m n h := by
  rw [specialFiberIdealIso, Iso.trans_hom, Category.assoc, subschemeCongr_hom_ι]
  exact Scheme.Hom.toImage_imageι _

/-- The same original polygon is the first parameter-power subscheme. -/
def specialFiberPowerOneIso : PolygonCyclicAtlas.scheme K n h ≅
    (stageParameterIdeal K m n h ^ 1).subscheme :=
  specialFiberIdealIso K m n h ≪≫ subschemeCongr (pow_one _).symm

/-- The power-one presentation also retains the original closed inclusion. -/
@[reassoc] theorem specialFiberPowerOneIso_hom_ι :
    (specialFiberPowerOneIso K m n h).hom ≫
      (stageParameterIdeal K m n h ^ 1).subschemeι = specialFiberInclusion K m n h := by
  rw [specialFiberPowerOneIso, Iso.trans_hom, Category.assoc, subschemeCongr_hom_ι,
    specialFiberIdealIso_hom_ι]

variable (L : (family K m n h).left.Modules) (hL : LocallyFreeRankOne L)

/-- The first parameter quotient is pullback to the actual original closed polygon. -/
def specialFiberLineQuotientIso : quotient (stageParameterIdeal K m n h) L 1 ≅
    (pushforward (specialFiberInclusion K m n h)).obj
      ((pullback (specialFiberInclusion K m n h)).obj L) :=
  ClosedLineQuotientPresentation.quotientIso (stageParameterIdeal K m n h) L hL 1
    (specialFiberPowerOneIso K m n h) (specialFiberInclusion K m n h)
    (specialFiberPowerOneIso_hom_ι K m n h)

/-- The quotient projection recovers the original closed restriction unit. -/
@[reassoc] theorem projection_specialFiberLineQuotientIso :
    projection (stageParameterIdeal K m n h) L 1 ≫
      (specialFiberLineQuotientIso K m n h L hL).hom =
        (pullbackPushforwardAdjunction (specialFiberInclusion K m n h)).unit.app L :=
  ClosedLineQuotientPresentation.projection_quotientIso _ _ _ _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
