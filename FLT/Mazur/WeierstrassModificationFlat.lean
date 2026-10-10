/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationAtlas
public import FLT.Mazur.WeierstrassModificationXFlat

/-!
# Flatness of the glued modification and its y-direction chart

Over a Bezout domain with nonzero scale, both original glued charts are flat.
Flatness descends through their open cover to the actual modification, and
then restricts to the proved y-direction open immersion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The actual structural map, retaining the contraction to the original cubic. -/
def modificationStructure : modification W s b3 b4 b6 ⟶ Spec (.of R) :=
  contraction W s b3 b4 b6 h3 h4 h6 ≫ WeierstrassIntegralChart.integralCurveStructure W

/-- The structural map restricts to the original x-chart algebra structure. -/
@[reassoc] theorem xChart_structure :
    xChart W s b3 b4 b6 ≫ modificationStructure W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6))) := by
  rw [modificationStructure, xChart_contraction_assoc, toCurve_structure]

/-- The structural map restricts to the original divided-chart algebra structure. -/
@[reassoc] theorem dividedChart_structure :
    dividedChart W s b3 b4 b6 ≫ modificationStructure W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (WeierstrassDilatation.Coordinate W s b3 b4 b6))) := by
  rw [modificationStructure, dividedChart_contraction_assoc,
    WeierstrassDilatation.toCurve_structure]

variable [IsDomain R] [IsBezout R]

/-- The whole constructed modification is flat over its original base. -/
theorem structure_flat (hs : s ≠ 0) : Flat (modificationStructure W s b3 b4 b6 h3 h4 h6) := by
  let _ := coordinate_flat_of_scale_ne_zero W s b3 b4 b6 hs
  have hx : Flat (xChart W s b3 b4 b6 ≫ modificationStructure W s b3 b4 b6 h3 h4 h6) := by
    rw [xChart_structure]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hd : Flat (dividedChart W s b3 b4 b6 ≫ modificationStructure W s b3 b4 b6 h3 h4 h6) := by
    rw [dividedChart_structure]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (Scheme.IsLocallyDirected.openCover
      (span (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6)))
  intro i
  cases i with
  | none =>
    change Flat (colimit.ι (span (xOpenInclusion W s b3 b4 b6)
      (overlapToDivided W s b3 b4 b6)) WalkingSpan.zero ≫ _)
    rw [← colimit.w _ WalkingSpan.Hom.fst, Category.assoc]
    change Flat (xOpenInclusion W s b3 b4 b6 ≫
      (xChart W s b3 b4 b6 ≫ modificationStructure W s b3 b4 b6 h3 h4 h6))
    let _ := hx
    infer_instance
  | some i =>
    cases i with
    | left => exact hx
    | right => exact hd

include h3 h4 h6 in
/-- The actual y-direction coordinate algebra is flat over the original base as well. -/
theorem yCoordinate_flat (hs : s ≠ 0) :
    Module.Flat R (WeierstrassModificationY.Coordinate W s b3 b4 b6) := by
  let _ := structure_flat W s b3 b4 b6 h3 h4 h6 hs
  have h : Flat (WeierstrassModificationY.yChart W s b3 b4 b6 ≫
      modificationStructure W s b3 b4 b6 h3 h4 h6) := inferInstance
  rw [modificationStructure, WeierstrassModificationY.yChart_contraction_assoc,
    WeierstrassModificationY.toCurve_structure] at h
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h)

end FLT.Mazur.WeierstrassModificationX
