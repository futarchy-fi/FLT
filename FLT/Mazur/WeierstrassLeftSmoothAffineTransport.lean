/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothProductOpen

/-!
# Transporting addition with a smooth first input to every input-chart overlap

The simultaneous affine overlap carries the enlarged affine law, allowing singular second inputs.
Its domain is exactly the smooth-input restriction induced from the original
projective input chart, so it is available in mixed and infinity covers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (b c : Bool)

/-- The left-smooth-input open in the simultaneous affine overlap of two projective charts. -/
def leftSmoothAffineOverlapOpen :
    (Spec (.of (ProductOverlap W
      (productChartCoordinate b) (productChartCoordinate c) 2 2))).Opens :=
  affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) ⁻¹ᵁ
    leftSmoothAffineInputOpen W

/-- The transported smooth domain is exactly the original input chart's smooth restriction. -/
theorem leftSmoothAffineOverlapOpen_eq :
    leftSmoothAffineOverlapOpen W b c =
      integralProductOverlapFst W b c false false ⁻¹ᵁ leftSmoothProductChartOpen W b c := by
  rw [leftSmoothProductChartOpen_overlap, leftSmoothProductChartOpen_affine]
  rfl

/-- The simultaneous normalization morphism between the actual left smooth input opens. -/
def leftSmoothAffineOverlapToInputs :
    (leftSmoothAffineOverlapOpen W b c).toScheme ⟶ (leftSmoothAffineInputOpen W).toScheme :=
  IsOpenImmersion.lift (leftSmoothAffineInputOpen W).ι
    ((leftSmoothAffineOverlapOpen W b c).ι ≫
      affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c)) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact p.property)

/-- Normalization retains the original simultaneous affine-overlap map. -/
@[reassoc] theorem leftSmoothAffineOverlapToInputs_inclusion :
    leftSmoothAffineOverlapToInputs W b c ≫ (leftSmoothAffineInputOpen W).ι =
      (leftSmoothAffineOverlapOpen W b c).ι ≫
        affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual original input pair of the transported smooth domain. -/
def leftSmoothAffineOverlapInput : (leftSmoothAffineOverlapOpen W b c).toScheme ⟶
    Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) :=
  (leftSmoothAffineOverlapOpen W b c).ι ≫ integralProductOverlapFst W b c false false

/-- The transported domain is open in the original input chart product. -/
instance leftSmoothAffineOverlapInput_isOpenImmersion :
    IsOpenImmersion (leftSmoothAffineOverlapInput W b c) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The enlarged affine law transported to this projective input overlap. -/
def leftSmoothAffineOverlapAddition :
    (leftSmoothAffineOverlapOpen W b c).toScheme ⟶ integralCurve W :=
  leftSmoothAffineOverlapToInputs W b c ≫ leftSmoothAffineAddition W

/-- The transported law is the original partial addition with its actual normalized inputs. -/
@[reassoc] theorem leftSmoothAffineOverlapAddition_partial :
    leftSmoothAffineOverlapAddition W b c =
      leftSmoothAffineOverlapToInputs W b c ≫ leftSmoothAffineInputToDomain W ≫
        affinePartialAddition W := rfl

end FLT.Mazur.WeierstrassIntegralChart
