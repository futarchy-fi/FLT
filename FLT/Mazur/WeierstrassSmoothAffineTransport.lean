/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothProductOpen

/-!
# Transporting smooth affine addition to every input-chart overlap

The simultaneous affine overlap carries the already glued smooth affine law.
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

/-- The smooth-input open in the simultaneous affine overlap of two projective charts. -/
def smoothAffineOverlapOpen :
    (Spec (.of (ProductOverlap W
      (productChartCoordinate b) (productChartCoordinate c) 2 2))).Opens :=
  affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) ⁻¹ᵁ
    smoothAffineInputOpen W

/-- The transported smooth domain is exactly the original input chart's smooth restriction. -/
theorem smoothAffineOverlapOpen_eq :
    smoothAffineOverlapOpen W b c =
      integralProductOverlapFst W b c false false ⁻¹ᵁ smoothProductChartOpen W b c := by
  rw [smoothProductChartOpen_overlap, smoothProductChartOpen_affine]
  rfl

/-- The simultaneous normalization morphism between the actual smooth input opens. -/
def smoothAffineOverlapToInputs :
    (smoothAffineOverlapOpen W b c).toScheme ⟶ (smoothAffineInputOpen W).toScheme :=
  IsOpenImmersion.lift (smoothAffineInputOpen W).ι
    ((smoothAffineOverlapOpen W b c).ι ≫
      affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c)) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact p.property)

/-- Normalization retains the original simultaneous affine-overlap map. -/
@[reassoc] theorem smoothAffineOverlapToInputs_inclusion :
    smoothAffineOverlapToInputs W b c ≫ (smoothAffineInputOpen W).ι =
      (smoothAffineOverlapOpen W b c).ι ≫
        affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual original input pair of the transported smooth domain. -/
def smoothAffineOverlapInput : (smoothAffineOverlapOpen W b c).toScheme ⟶
    Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) :=
  (smoothAffineOverlapOpen W b c).ι ≫ integralProductOverlapFst W b c false false

/-- The transported domain is open in the original input chart product. -/
instance smoothAffineOverlapInput_isOpenImmersion :
    IsOpenImmersion (smoothAffineOverlapInput W b c) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The full smooth affine law transported to this projective input overlap. -/
def smoothAffineOverlapAddition :
    (smoothAffineOverlapOpen W b c).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  smoothAffineOverlapToInputs W b c ≫ smoothAffineAddition W

/-- The transported law is still the original partial addition in normalized affine inputs. -/
@[reassoc] theorem smoothAffineOverlapAddition_partial :
    smoothAffineOverlapAddition W b c ≫ (integralSmoothOpen W).ι =
      smoothAffineOverlapToInputs W b c ≫ smoothAffineInputToDomain W ≫
        affinePartialAddition W := by
  rw [smoothAffineOverlapAddition, Category.assoc, smoothAffineAddition_partial]

end FLT.Mazur.WeierstrassIntegralChart
