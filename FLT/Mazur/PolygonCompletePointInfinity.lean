/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointProjectiveIso
public import FLT.Mazur.WeierstrassNonzeroPointAffine

/-!
# The retained marking goes to infinity

The projective isomorphism identifies the entire retained-point complement
with the original affine chart. Hence the image of the marking cannot lie in
that chart. The field-point classification then identifies its scheme morphism
with the actual infinity section over the unchanged field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The image of the retained marking is outside the original affine chart. -/
theorem completeCartesianPointToProjective_marking_not_affine (i : Fin n)
    (x : Spec (.of L)) :
    completeCartesianPointToProjective K n h L a ha p q hs i
      (completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs i x) ∉
      Set.range (integralCurveChart (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) 2) := by
  let W := completeCartesianPointWeierstrass K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i
  let U := completeCartesianPointComplement K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i
  let f := completeCartesianPointToProjective K n h L a ha p q hs i
  let e := completeCartesianSmoothPointAffineIso K n h L a ha p q hs i
  let _ : IsIso f := completeCartesianPointToProjective_isIso K n h L a ha p q hs i
  have hc : (monicChartIso W).inv ≫ e.inv ≫ U.ι ≫ f = integralCurveChart W 2 := by
    rw [completeCartesianPointToProjective_restrict]
    change _ ≫ _ ≫ (e.hom ≫ (monicChartIso W).hom ≫ integralCurveChart W 2) = _
    simp only [Iso.inv_hom_id_assoc]
  rintro ⟨z, hz⟩
  let v := e.inv ((monicChartIso W).inv z)
  have hv : U.ι v = completeCartesianMarking K n h
      (Spec.map (CommRingCat.ofHom a)) p q hs i x := by
    apply f.isOpenEmbedding.injective
    exact (congrArg (fun t ↦ t z) hc).trans hz
  have hm := v.2
  change U.ι v ∈ U at hm
  rw [hv] at hm
  change _ ∉ ((completeCartesianMarking K n h
    (Spec.map (CommRingCat.ofHom a)) p q hs i).ker.support : Set Y) at hm
  rw [completeCartesianMarking_support] at hm
  exact hm ⟨x, rfl⟩

/-- The projective isomorphism preserves the retained point as the actual infinity section. -/
theorem completeCartesianPointToProjective_marking (i : Fin n) :
    completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs i ≫
      completeCartesianPointToProjective K n h L a ha p q hs i =
      integralCurveZero (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) := by
  classical
  let W := completeCartesianPointWeierstrass K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i
  let _ : W.IsElliptic := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
  let hΔ := WeierstrassCurve.isUnit_Δ W
  let P : integralGroupFieldPoints (K := L) W hΔ :=
    Over.homMk (completeCartesianMarking K n h
      (Spec.map (CommRingCat.ofHom a)) p q hs i ≫
        completeCartesianPointToProjective K n h L a ha p q hs i) (by
      change _ ≫ integralCurveStructure W = _
      rw [Category.assoc, completeCartesianPointToProjective_over,
        completeCartesianMarking_snd]
      simp)
  have hP : P = 1 := by
    by_contra hP
    obtain ⟨t, ht⟩ := nonzeroPoint_factor W hΔ P hP
    let x : Spec (.of L) := ⟨⊥, inferInstance⟩
    exact completeCartesianPointToProjective_marking_not_affine K n h L a ha p q hs i x
      ⟨t x, congrArg (fun z ↦ z x) ht⟩
  have he := congrArg (fun z : integralGroupFieldPoints (K := L) W hΔ ↦ z.left) hP
  change completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs i ≫
    completeCartesianPointToProjective K n h L a ha p q hs i =
      Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ integralCurveZero W at he
  simpa using he

end FLT.Mazur.PolygonInfinitesimalStages
