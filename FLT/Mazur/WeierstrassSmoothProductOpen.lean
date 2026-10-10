/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineAddition
public import FLT.Mazur.WeierstrassIntegralProductOverlap

/-!
# The smooth input open in the full projective product

The four Y/Z tensor charts restrict to the locus where both curve inputs are
relatively smooth. Their overlap restrictions agree, and the all-affine member
is exactly the smooth affine domain on which addition has already been glued.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual open of the projective input product where both factors are smooth. -/
def smoothCurveProductOpen : (integralCurveProduct W).Opens :=
  pullback.fst (integralCurveStructure W) (integralCurveStructure W) ⁻¹ᵁ
      integralSmoothOpen W ⊓
    pullback.snd (integralCurveStructure W) (integralCurveStructure W) ⁻¹ᵁ
      integralSmoothOpen W

/-- The smooth input restriction of one of the four original tensor-product charts. -/
def smoothProductChartOpen (b c : Bool) :
    (Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))).Opens :=
  integralCurveProductChart W b c ⁻¹ᵁ smoothCurveProductOpen W

/-- In each tensor chart the smooth input condition is the pair of relative chart conditions. -/
theorem smoothProductChartOpen_eq (b c : Bool) :
    smoothProductChartOpen W b c =
      Spec.map (CommRingCat.ofHom
        (chartProductLeft W (productChartCoordinate b) (productChartCoordinate c)).toRingHom) ⁻¹ᵁ
          (chartStructure W (productChartCoordinate b)).smoothLocus ⊓
        Spec.map (CommRingCat.ofHom
          (chartProductRight W (productChartCoordinate b) (productChartCoordinate c)).toRingHom)
            ⁻¹ᵁ (chartStructure W (productChartCoordinate c)).smoothLocus := by
  simp only [smoothProductChartOpen, smoothCurveProductOpen, Scheme.Hom.preimage_inf,
    ← Scheme.Hom.comp_preimage, integralCurveProductChart_fst, integralCurveProductChart_snd]
  simp only [Scheme.Hom.comp_preimage, integralCurveChart_preimage_smooth]

/-- The all-affine projective product restriction is the already constructed smooth domain. -/
theorem smoothProductChartOpen_affine :
    smoothProductChartOpen W false false = smoothAffineInputOpen W := by
  rw [smoothProductChartOpen_eq]
  rfl

/-- Smooth input conditions are invariant under simultaneous changes of input coordinates. -/
theorem smoothProductChartOpen_overlap (b c d e : Bool) :
    integralProductOverlapFst W b c d e ⁻¹ᵁ smoothProductChartOpen W b c =
      integralProductOverlapSnd W b c d e ⁻¹ᵁ smoothProductChartOpen W d e := by
  simp only [smoothProductChartOpen, ← Scheme.Hom.comp_preimage]
  rw [integralProductOverlap_condition]

/-- The original four tensor charts pulled back to the full smooth projective input open. -/
def smoothCurveProductCover : (smoothCurveProductOpen W).toScheme.OpenCover :=
  (integralCurveProductCover W).pullback₁ (smoothCurveProductOpen W).ι

/-- The pulled-back product cover retains the actual original tensor charts. -/
def smoothCurveProductCoverProjection (b c : Bool) :
    (smoothCurveProductCover W).X (b, c) ⟶
      Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))) :=
  (integralCurveProductCover W).pullbackHom (smoothCurveProductOpen W).ι (b, c)

/-- The two routes to the original projective input product coincide. -/
@[reassoc] theorem smoothCurveProductCoverProjection_inputs (b c : Bool) :
    smoothCurveProductCoverProjection W b c ≫ integralCurveProductChart W b c =
      (smoothCurveProductCover W).f (b, c) ≫ (smoothCurveProductOpen W).ι :=
  Scheme.Cover.pullbackHom_map (integralCurveProductCover W) (smoothCurveProductOpen W).ι (b, c)

end FLT.Mazur.WeierstrassIntegralChart
