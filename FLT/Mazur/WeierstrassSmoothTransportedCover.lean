/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineTransport
public import FLT.Mazur.WeierstrassTransportedComparisonArbitrary

/-!
# Original tensor domains covering transported smooth addition

Pull back the four smooth affine charts along simultaneous normalization.
Each member maps to the original transported tensor domain, retaining both
its input morphism and its addition output. This connects smooth gluing to
the existing polynomial and infinity overlap identities.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (b c : Bool)

/-- Pull back the four smooth affine charts to the simultaneous input overlap. -/
def smoothTransportedCover : (smoothAffineOverlapOpen W b c).toScheme.OpenCover :=
  (smoothAffineAdditionCover W).pullback₁ (smoothAffineOverlapToInputs W b c)

/-- The projection to the corresponding smooth affine chart. -/
def smoothTransportedAffineProjection (i : AdditionChartIndex) :
    (smoothTransportedCover W b c).X i ⟶ (smoothAffineAdditionCover W).X i :=
  (smoothAffineAdditionCover W).pullbackHom (smoothAffineOverlapToInputs W b c) i

/-- The two projections give the same normalized affine input pair. -/
theorem smoothTransportedAffineProjection_inputs (i : AdditionChartIndex) :
    (smoothTransportedAffineProjection W b c i ≫ smoothAffineAdditionProjection W i) ≫
        additionChartInclusion W i =
      ((smoothTransportedCover W b c).f i ≫ (smoothAffineOverlapOpen W b c).ι) ≫
        affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) := by
  rw [Category.assoc, smoothAffineAdditionProjection_inputs, ← Category.assoc]
  change ((smoothAffineAdditionCover W).pullbackHom (smoothAffineOverlapToInputs W b c) i ≫
    (smoothAffineAdditionCover W).f i) ≫ _ = _
  rw [Scheme.Cover.pullbackHom_map, Category.assoc, smoothAffineOverlapToInputs_inclusion]
  rfl

/-- The actual map from a covering chart to its original transported tensor domain. -/
def smoothTransportedRawProjection (i : AdditionChartIndex) :
    (smoothTransportedCover W b c).X i ⟶ Spec (.of
      (TransportedAdditionRing W (productChartCoordinate b) (productChartCoordinate c) i)) :=
  IsPullback.lift
    (transportedAdditionRing_isPullback W (productChartCoordinate b) (productChartCoordinate c) i)
    ((smoothTransportedCover W b c).f i ≫ (smoothAffineOverlapOpen W b c).ι)
      (smoothTransportedAffineProjection W b c i ≫ smoothAffineAdditionProjection W i)
      (smoothTransportedAffineProjection_inputs W b c i).symm

/-- The raw projection recovers the actual original affine addition chart. -/
@[reassoc] theorem smoothTransportedRawProjection_affine (i : AdditionChartIndex) :
    smoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionAffine W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) =
      smoothTransportedAffineProjection W b c i ≫ smoothAffineAdditionProjection W i :=
  (transportedAdditionRing_isPullback W (productChartCoordinate b)
    (productChartCoordinate c) i).lift_snd _ _ _

/-- The raw projection recovers the original simultaneous input overlap. -/
@[reassoc] theorem smoothTransportedRawProjection_overlap (i : AdditionChartIndex) :
    smoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionOverlap W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) =
      (smoothTransportedCover W b c).f i ≫ (smoothAffineOverlapOpen W b c).ι :=
  (transportedAdditionRing_isPullback W (productChartCoordinate b)
    (productChartCoordinate c) i).lift_fst _ _ _

/-- The original transported tensor map retains the input-chart pair exactly. -/
@[reassoc] theorem smoothTransportedRawProjection_inputs (i : AdditionChartIndex) :
    smoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionInput W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) =
      (smoothTransportedCover W b c).f i ≫ smoothAffineOverlapInput W b c := by
  have h : Spec.map (CommRingCat.ofHom
      (transportedAdditionInput W (productChartCoordinate b)
        (productChartCoordinate c) i).toRingHom) =
      Spec.map (CommRingCat.ofHom (transportedAdditionOverlap W (productChartCoordinate b)
        (productChartCoordinate c) i).toRingHom) ≫ integralProductOverlapFst W b c false false := by
    rw [← Spec.map_comp]
    rfl
  rw [h, smoothTransportedRawProjection_overlap_assoc]
  rfl

/-- The original tensor-domain output is the restriction of the glued smooth law. -/
@[reassoc] theorem smoothTransportedRawProjection_addition (i : AdditionChartIndex) :
    smoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionAffine W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) ≫ additionCurveChart W i =
      (smoothTransportedCover W b c).f i ≫ smoothAffineOverlapAddition W b c ≫
        (integralSmoothOpen W).ι := by
  rw [smoothTransportedRawProjection_affine_assoc]
  have hl : smoothAffineAdditionLocal W i ≫ (integralSmoothOpen W).ι =
      smoothAffineAdditionProjection W i ≫ additionCurveChart W i := by
    rw [smoothAffineAdditionLocal, Category.assoc, additionSmoothChart_inclusion,
      smoothAffineAdditionLift_inclusion_assoc]
  rw [← hl, ← smoothAffineAdditionLocal_glued]
  have h : smoothTransportedAffineProjection W b c i ≫ (smoothAffineAdditionCover W).f i =
      (smoothTransportedCover W b c).f i ≫ smoothAffineOverlapToInputs W b c :=
    Scheme.Cover.pullbackHom_map _ _ _
  simp only [Category.assoc]
  rw [← Category.assoc (smoothTransportedAffineProjection W b c i), h]
  simp only [Category.assoc, smoothAffineOverlapAddition]

end FLT.Mazur.WeierstrassIntegralChart
