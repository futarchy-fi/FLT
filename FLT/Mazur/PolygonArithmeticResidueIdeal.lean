/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ClosedLineQuotientPresentation
public import FLT.Mazur.PolygonArithmeticResidueKernel
public import FLT.Mazur.PolygonArithmeticStageLineQuotient

/-!
# The original closed polygon as the parameter subscheme

The original special-fiber inclusion has exactly the extended parameter
ideal as kernel. The resulting line quotient comparison preserves its unit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve BaseAdicThickening IdealAdicQuotient Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (hπ : algebraMap A (IsLocalRing.ResidueField A) π = 0) (m n : ℕ) (h : 2 ≤ n)
local notation "K" => IsLocalRing.ResidueField A

include hgen in
/-- The coefficient closed-fiber map has the actual principal ideal sheaf as kernel. -/
theorem residueBase_ker : (residueBase A π hπ m).ker =
    baseIdeal (.of (Quotient A π m)) (Ideal.span {parameter A π m}) := by
  rw [residueBase, specMap_ker_baseIdeal]
  change baseIdeal (.of (Quotient A π m)) (RingHom.ker (residueMap A π hπ m)) = _
  rw [residueMap_ker A π hgen hπ m]

include hgen in
/-- The original closed polygon is cut out by the actual stage parameter. -/
theorem residueFiberInclusion_ker : (residueFiberInclusion A π hπ m n h).ker =
    stageParameterIdeal A π m n h := by
  rw [← residueFiberIso_fst A π hπ m n h, Scheme.Hom.ker_comp_of_isIso,
    ker_fst_of_isClosedImmersion, residueBase_ker A π hgen]
  rfl

/-- The original polygon identifies with the actual parameter subscheme. -/
def residueFiberIdealIso : PolygonCyclicAtlas.scheme K n h ≅
    (stageParameterIdeal A π m n h).subscheme :=
  asIso (residueFiberInclusion A π hπ m n h).toImage ≪≫
    subschemeCongr (residueFiberInclusion_ker A π hgen hπ m n h)

/-- The identification retains the specified closed polygon inclusion. -/
@[reassoc] theorem residueFiberIdealIso_hom_ι :
    (residueFiberIdealIso A π hgen hπ m n h).hom ≫ (stageParameterIdeal A π m n h).subschemeι =
      residueFiberInclusion A π hπ m n h := by
  rw [residueFiberIdealIso, Iso.trans_hom, Category.assoc, subschemeCongr_hom_ι]
  exact Scheme.Hom.toImage_imageι _

/-- The same original polygon is the first parameter-power subscheme. -/
def residueFiberPowerOneIso : PolygonCyclicAtlas.scheme K n h ≅
    (stageParameterIdeal A π m n h ^ 1).subscheme :=
  residueFiberIdealIso A π hgen hπ m n h ≪≫ subschemeCongr (pow_one _).symm

/-- The power-one presentation also retains the original closed inclusion. -/
@[reassoc] theorem residueFiberPowerOneIso_hom_ι :
    (residueFiberPowerOneIso A π hgen hπ m n h).hom ≫
      (stageParameterIdeal A π m n h ^ 1).subschemeι = residueFiberInclusion A π hπ m n h := by
  rw [residueFiberPowerOneIso, Iso.trans_hom, Category.assoc, subschemeCongr_hom_ι,
    residueFiberIdealIso_hom_ι]

variable (L : (family A π m n h).left.Modules) (hL : LocallyFreeRankOne L)

/-- The first parameter quotient is pullback to the actual original closed polygon. -/
def residueFiberLineQuotientIso : quotient (stageParameterIdeal A π m n h) L 1 ≅
    (pushforward (residueFiberInclusion A π hπ m n h)).obj
      ((pullback (residueFiberInclusion A π hπ m n h)).obj L) :=
  ClosedLineQuotientPresentation.quotientIso (stageParameterIdeal A π m n h) L hL 1
    (residueFiberPowerOneIso A π hgen hπ m n h) (residueFiberInclusion A π hπ m n h)
    (residueFiberPowerOneIso_hom_ι A π hgen hπ m n h)

/-- The quotient projection recovers the original closed restriction unit. -/
@[reassoc] theorem projection_residueFiberLineQuotientIso :
    projection (stageParameterIdeal A π m n h) L 1 ≫
      (residueFiberLineQuotientIso A π hgen hπ m n h L hL).hom =
        (pullbackPushforwardAdjunction (residueFiberInclusion A π hπ m n h)).unit.app L :=
  ClosedLineQuotientPresentation.projection_quotientIso _ _ _ _ _ _ _

end FLT.Mazur.PolygonArithmeticStages
