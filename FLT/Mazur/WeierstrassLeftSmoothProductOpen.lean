/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAffineAddition
public import FLT.Mazur.WeierstrassIntegralProductOverlap

/-!
# The left smooth input open in the full projective product

The four Y/Z tensor charts restrict to the locus where the first curve input is
relatively smooth. Their overlap restrictions agree, and the all-affine member
is exactly the left smooth affine domain on which addition has already been glued.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual open of the projective input product where the first factor is smooth. -/
def leftSmoothCurveProductOpen : (integralCurveProduct W).Opens :=
  pullback.fst (integralCurveStructure W) (integralCurveStructure W) ⁻¹ᵁ
      integralSmoothOpen W

/-- The smooth input restriction of one of the four original tensor-product charts. -/
def leftSmoothProductChartOpen (b c : Bool) :
    (Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))).Opens :=
  integralCurveProductChart W b c ⁻¹ᵁ leftSmoothCurveProductOpen W

/-- In each tensor chart the smooth input condition is the first relative chart condition. -/
theorem leftSmoothProductChartOpen_eq (b c : Bool) :
    leftSmoothProductChartOpen W b c =
      Spec.map (CommRingCat.ofHom
        (chartProductLeft W (productChartCoordinate b) (productChartCoordinate c)).toRingHom) ⁻¹ᵁ
          (chartStructure W (productChartCoordinate b)).smoothLocus := by
  simp only [leftSmoothProductChartOpen, leftSmoothCurveProductOpen,
    ← Scheme.Hom.comp_preimage, integralCurveProductChart_fst]
  simp only [Scheme.Hom.comp_preimage, integralCurveChart_preimage_smooth]

/-- The all-affine projective product restriction is the already constructed smooth domain. -/
theorem leftSmoothProductChartOpen_affine :
    leftSmoothProductChartOpen W false false = leftSmoothAffineInputOpen W := by
  rw [leftSmoothProductChartOpen_eq]
  rfl

/-- Smooth input conditions are invariant under simultaneous changes of input coordinates. -/
theorem leftSmoothProductChartOpen_overlap (b c d e : Bool) :
    integralProductOverlapFst W b c d e ⁻¹ᵁ leftSmoothProductChartOpen W b c =
      integralProductOverlapSnd W b c d e ⁻¹ᵁ leftSmoothProductChartOpen W d e := by
  simp only [leftSmoothProductChartOpen, ← Scheme.Hom.comp_preimage]
  rw [integralProductOverlap_condition]

/-- The original four tensor charts pulled back to the full smooth projective input open. -/
def leftSmoothCurveProductCover : (leftSmoothCurveProductOpen W).toScheme.OpenCover :=
  (integralCurveProductCover W).pullback₁ (leftSmoothCurveProductOpen W).ι

/-- The pulled-back product cover retains the actual original tensor charts. -/
def leftSmoothCurveProductCoverProjection (b c : Bool) :
    (leftSmoothCurveProductCover W).X (b, c) ⟶
      Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) :=
  (integralCurveProductCover W).pullbackHom (leftSmoothCurveProductOpen W).ι (b, c)

/-- The two routes to the original projective input product coincide. -/
@[reassoc] theorem leftSmoothCurveProductCoverProjection_inputs (b c : Bool) :
    leftSmoothCurveProductCoverProjection W b c ≫ integralCurveProductChart W b c =
      (leftSmoothCurveProductCover W).f (b, c) ≫ (leftSmoothCurveProductOpen W).ι :=
  Scheme.Cover.pullbackHom_map (integralCurveProductCover W) (leftSmoothCurveProductOpen W).ι (b, c)

end FLT.Mazur.WeierstrassIntegralChart
