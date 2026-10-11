/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAffineTransport
public import FLT.Mazur.WeierstrassTransportedComparisonArbitrary

/-!
# Original tensor domains for translation with singular second inputs

Pull back the four affine charts with smooth first inputs along simultaneous normalization.
Each member maps to the original transported tensor domain, retaining both
its input morphism and its addition output. This connects integral gluing to
the existing polynomial and infinity overlap identities.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (b c : Bool)

/-- Pull back the four affine charts with smooth first inputs to the simultaneous input overlap. -/
def leftSmoothTransportedCover : (leftSmoothAffineOverlapOpen W b c).toScheme.OpenCover :=
  (leftSmoothAffineAdditionCover W).pullback₁ (leftSmoothAffineOverlapToInputs W b c)

/-- The projection to the corresponding smooth affine chart. -/
def leftSmoothTransportedAffineProjection (i : AdditionChartIndex) :
    (leftSmoothTransportedCover W b c).X i ⟶ (leftSmoothAffineAdditionCover W).X i :=
  (leftSmoothAffineAdditionCover W).pullbackHom (leftSmoothAffineOverlapToInputs W b c) i

/-- The two projections give the same normalized affine input pair. -/
theorem leftSmoothTransportedAffineProjection_inputs (i : AdditionChartIndex) :
    (leftSmoothTransportedAffineProjection W b c i ≫ leftSmoothAffineAdditionProjection W i) ≫
        additionChartInclusion W i =
      ((leftSmoothTransportedCover W b c).f i ≫ (leftSmoothAffineOverlapOpen W b c).ι) ≫
        affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) := by
  rw [Category.assoc, leftSmoothAffineAdditionProjection_inputs, ← Category.assoc]
  change ((leftSmoothAffineAdditionCover W).pullbackHom (leftSmoothAffineOverlapToInputs W b c) i ≫
    (leftSmoothAffineAdditionCover W).f i) ≫ _ = _
  rw [Scheme.Cover.pullbackHom_map, Category.assoc, leftSmoothAffineOverlapToInputs_inclusion]
  rfl

/-- The actual map from a covering chart to its original transported tensor domain. -/
def leftSmoothTransportedRawProjection (i : AdditionChartIndex) :
    (leftSmoothTransportedCover W b c).X i ⟶ Spec (.of
      (TransportedAdditionRing W (productChartCoordinate b) (productChartCoordinate c) i)) :=
  IsPullback.lift
    (transportedAdditionRing_isPullback W (productChartCoordinate b) (productChartCoordinate c) i)
    ((leftSmoothTransportedCover W b c).f i ≫ (leftSmoothAffineOverlapOpen W b c).ι)
      (leftSmoothTransportedAffineProjection W b c i ≫ leftSmoothAffineAdditionProjection W i)
      (leftSmoothTransportedAffineProjection_inputs W b c i).symm

/-- The raw projection recovers the actual original affine addition chart. -/
@[reassoc] theorem leftSmoothTransportedRawProjection_affine (i : AdditionChartIndex) :
    leftSmoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionAffine W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) =
      leftSmoothTransportedAffineProjection W b c i ≫ leftSmoothAffineAdditionProjection W i :=
  (transportedAdditionRing_isPullback W (productChartCoordinate b)
    (productChartCoordinate c) i).lift_snd _ _ _

/-- The raw projection recovers the original simultaneous input overlap. -/
@[reassoc] theorem leftSmoothTransportedRawProjection_overlap (i : AdditionChartIndex) :
    leftSmoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionOverlap W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) =
      (leftSmoothTransportedCover W b c).f i ≫ (leftSmoothAffineOverlapOpen W b c).ι :=
  (transportedAdditionRing_isPullback W (productChartCoordinate b)
    (productChartCoordinate c) i).lift_fst _ _ _

/-- The original transported tensor map retains the input-chart pair exactly. -/
@[reassoc] theorem leftSmoothTransportedRawProjection_inputs (i : AdditionChartIndex) :
    leftSmoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionInput W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) =
      (leftSmoothTransportedCover W b c).f i ≫ leftSmoothAffineOverlapInput W b c := by
  have h : Spec.map (CommRingCat.ofHom
      (transportedAdditionInput W (productChartCoordinate b)
        (productChartCoordinate c) i).toRingHom) =
      Spec.map (CommRingCat.ofHom (transportedAdditionOverlap W (productChartCoordinate b)
        (productChartCoordinate c) i).toRingHom) ≫ integralProductOverlapFst W b c false false := by
    rw [← Spec.map_comp]
    rfl
  rw [h, leftSmoothTransportedRawProjection_overlap_assoc]
  rfl

/-- The original tensor-domain output is the restriction of the enlarged affine law. -/
@[reassoc] theorem leftSmoothTransportedRawProjection_addition (i : AdditionChartIndex) :
    leftSmoothTransportedRawProjection W b c i ≫ Spec.map (CommRingCat.ofHom
        (transportedAdditionAffine W (productChartCoordinate b) (productChartCoordinate c)
          i).toRingHom) ≫ additionCurveChart W i =
      (leftSmoothTransportedCover W b c).f i ≫ leftSmoothAffineOverlapAddition W b c := by
  rw [leftSmoothTransportedRawProjection_affine_assoc]
  rw [leftSmoothAffineAdditionProjection_addition]
  have h : leftSmoothTransportedAffineProjection W b c i ≫
      (leftSmoothAffineAdditionCover W).f i =
      (leftSmoothTransportedCover W b c).f i ≫ leftSmoothAffineOverlapToInputs W b c :=
    Scheme.Cover.pullbackHom_map _ _ _
  rw [← Category.assoc (leftSmoothTransportedAffineProjection W b c i), h]
  simp only [Category.assoc, leftSmoothAffineOverlapAddition]

end FLT.Mazur.WeierstrassIntegralChart
