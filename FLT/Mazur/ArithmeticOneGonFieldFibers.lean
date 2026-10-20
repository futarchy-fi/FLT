/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingFieldFibers

/-!
# Field fibers of arithmetic one-gon degenerations

Over any coefficient ring, invertibility of the complementary discriminant
factor separates every field fiber into the original nodal one-gon or a smooth
cubic. This includes mixed-characteristic bases and their nonreduced tests.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonFieldFibers

open OneGonSmoothing WeierstrassIntegralChart FCurve FCurve.DRFiberClassification

variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))
  (L : Type) [Field L]

include ht

/-- Nonzero parameter gives an elliptic cubic over every field-valued coefficient map. -/
theorem field_isElliptic (a : R →+* L) (ha : a t ≠ 0) :
    ((equation t).map a).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  rw [WeierstrassCurve.map_Δ, equation_discriminant, map_mul, map_neg]
  exact mul_ne_zero (neg_ne_zero.mpr ha) (ht.map a).ne_zero

/-- Any specified nonzero-parameter field square is smooth of relative dimension one. -/
theorem cartesian_relativeDimension (a : R →+* L) (ha : a t ≠ 0) {Y : Scheme}
    (p : Y ⟶ (family t).left) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (family t).hom (Spec.map (CommRingCat.ofHom a))) :
    SmoothOfRelativeDimension 1 q := by
  let _ := a.toAlgebra
  let hc := coefficient_isPullback (S := L) t
  let e := hs.isoIsPullback _ _ hc
  have he : e.hom ≫ (family (a t)).hom = q := hs.isoIsPullback_hom_snd _ _ hc
  have hell := field_isElliptic t ht L a ha
  rw [equation_map] at hell
  let _ : SmoothOfRelativeDimension 1 (family (a t)).hom :=
    integralCurveStructure_smooth_dimension _ hell.isUnit
  rw [← he]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) inferInstance e.hom

variable (s : Spec (.of L) ⟶ Spec (.of R)) {Y : Scheme}
  (p : Y ⟶ (family t).left) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (family t).hom s)

include hs

/-- Every field square has the actual smooth-or-one-gon classification. -/
theorem cartesian_classified : ClassifiedFiberCore q := by
  let a := (Spec.preimage s).hom
  have he : Spec.map (CommRingCat.ofHom a) = s := Spec.map_preimage s
  have hs' : IsPullback p q (family t).hom (Spec.map (CommRingCat.ofHom a)) := he.symm ▸ hs
  by_cases ha : a t = 0
  · let _ := a.toAlgebra
    exact zeroCartesian_classified L t ha p q hs'
  · let _ := cartesian_relativeDimension t ht L a ha p q hs'
    let _ := SmoothOfRelativeDimension.smooth 1 q
    let _ := integralCurveFieldSquare_isIntegral (equation t) s p q hs
    let _ := family_proper t
    let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
    let _ := Chow.source_isNoetherian q
    exact ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance,
      smoothCurvePureDimension q, CurveFiberHypotheses.nodes_of_smoothFiber q⟩,
        Or.inl inferInstance⟩

omit ht in
/-- Field-square constants are computed on the original arithmetic cubic. -/
theorem cartesian_constantSections : HasConstantGlobalSections q :=
  integralCurveFieldSquare_constantGlobalSections (equation t) s p q hs

omit ht in
/-- Field-square first cohomology has dimension one over the actual field. -/
theorem cartesianH1_finrank : Module.finrank L (H1 q) = 1 :=
  integralCurveFieldSquareH1_finrank (equation t) s p q hs

end FLT.Mazur.ArithmeticOneGonFieldFibers
