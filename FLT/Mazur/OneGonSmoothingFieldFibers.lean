/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingZeroGenus
public import FLT.Mazur.WeierstrassGenusOneFamily
public import FLT.Mazur.SmoothCurvePureDimension

/-!
# Field fibers of the complete one-gon smoothing

The original parameter separates the nodal one-gon from smooth curves.
The cubic cohomology calculation supplies constants and actual H1 on every
specified field square, including the nonzero-parameter fibers.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open FCurve FCurve.CurveFiberHypotheses FCurve.DRFiberClassification
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K L : Type) [Field K] [Field L]

/-- Every specified nonzero-parameter field square is smooth of relative dimension one. -/
theorem completeCartesian_relativeDimension (a : PowerSeries K →+* L)
    (ha : a PowerSeries.X ≠ 0) {Y : Scheme}
    (p : Y ⟶ (family (PowerSeries.X : PowerSeries K)).left) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (family (PowerSeries.X : PowerSeries K)).hom
      (Spec.map (CommRingCat.ofHom a))) : SmoothOfRelativeDimension 1 q := by
  let _ := a.toAlgebra
  let hc := coefficient_isPullback (S := L) (PowerSeries.X : PowerSeries K)
  let e := hs.isoIsPullback _ _ hc
  have he : e.hom ≫ (family (a PowerSeries.X)).hom = q :=
    hs.isoIsPullback_hom_snd _ _ hc
  let _ := fieldFamily_smooth_dimension K L a ha
  rw [← he]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) inferInstance e.hom

variable (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K))) {Y : Scheme}
  (p : Y ⟶ (family (PowerSeries.X : PowerSeries K)).left) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (family (PowerSeries.X : PowerSeries K)).hom s)

include hs

/-- Every field fiber retains its actual nodal geometry and smooth-or-one-gon classification. -/
theorem completeCartesian_classified : ClassifiedFiberCore q := by
  let a := (Spec.preimage s).hom
  have he : Spec.map (CommRingCat.ofHom a) = s := Spec.map_preimage s
  have hs' : IsPullback p q (family (PowerSeries.X : PowerSeries K)).hom
      (Spec.map (CommRingCat.ofHom a)) := he.symm ▸ hs
  by_cases ha : a PowerSeries.X = 0
  · let _ := a.toAlgebra
    exact zeroCartesian_classified L PowerSeries.X ha p q hs'
  · let _ := completeCartesian_relativeDimension K L a ha p q hs'
    let _ := SmoothOfRelativeDimension.smooth 1 q
    let _ := integralCurveFieldSquare_isIntegral (equation (PowerSeries.X : PowerSeries K))
      s p q hs
    let _ := family_proper (PowerSeries.X : PowerSeries K)
    let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
    let _ := Chow.source_isNoetherian q
    exact ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance,
      smoothCurvePureDimension q, nodes_of_smoothFiber q⟩, Or.inl inferInstance⟩

/-- Every specified complete-family field square has exactly its base-field constants. -/
theorem completeCartesian_constantSections : HasConstantGlobalSections q :=
  integralCurveFieldSquare_constantGlobalSections (equation (PowerSeries.X : PowerSeries K))
    s p q hs

/-- Every specified complete-family field square has actual first cohomology of dimension one. -/
theorem completeCartesianH1_finrank : Module.finrank L (H1 q) = 1 :=
  integralCurveFieldSquareH1_finrank (equation (PowerSeries.X : PowerSeries K)) s p q hs

end FLT.Mazur.OneGonSmoothing
