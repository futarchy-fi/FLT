/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedAffinePoints

/-!
# Original labels as distinct field points of the constructed elliptic curve

Transport every original marking by the proved projective isomorphism. Their
pairwise disjointness makes this a genuine injection into the field-point group,
and precisely the retained label is the identity. No cyclic group law on the
labels is assumed or claimed here.
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

/-- Every retained label defines its actual point of the original constructed elliptic group. -/
def completeCartesianProjectiveMarkedPoint (i j : Fin n) :
    integralGroupFieldPoints (K := L)
      (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i)
      (by
        let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
        exact WeierstrassCurve.isUnit_Δ _) :=
  Over.homMk (completeCartesianMarking K n h
    (Spec.map (CommRingCat.ofHom a)) p q hs j ≫
      completeCartesianPointToProjective K n h L a ha p q hs i) (by
    change _ ≫ integralCurveStructure _ = _
    rw [Category.assoc, completeCartesianPointToProjective_over, completeCartesianMarking_snd]
    simp)

/-- The retained infinity label is the identity of the actual field-point group. -/
theorem completeCartesianProjectiveMarkedPoint_self (i : Fin n) :
    completeCartesianProjectiveMarkedPoint K n h L a ha p q hs i i = 1 := by
  apply Over.OverMorphism.ext
  change completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs i ≫
    completeCartesianPointToProjective K n h L a ha p q hs i =
      Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ integralCurveZero _
  simpa using completeCartesianPointToProjective_marking K n h L a ha p q hs i

/-- Distinct original labels remain distinct points of the constructed projective group. -/
theorem completeCartesianProjectiveMarkedPoint_injective (i : Fin n) :
    Function.Injective (completeCartesianProjectiveMarkedPoint K n h L a ha p q hs i) := by
  intro j k hjk
  let _ := completeCartesianPointToProjective_isIso K n h L a ha p q hs i
  have hm : completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs j =
      completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs k :=
    (cancel_mono (completeCartesianPointToProjective K n h L a ha p q hs i)).mp
      (congrArg (fun z ↦ z.left) hjk)
  by_contra hne
  have hd := completeCartesianMarkings_pairwise K n h
    (Spec.map (CommRingCat.ofHom a)) p q hs hne
  let x : Spec (.of L) := ⟨⊥, inferInstance⟩
  exact Set.disjoint_left.mp hd ⟨x, rfl⟩ ⟨x, congrArg (fun z ↦ z x) hm.symm⟩

/-- Among the original labels, exactly the retained label maps to the identity. -/
theorem completeCartesianProjectiveMarkedPoint_eq_one_iff (i j : Fin n) :
    completeCartesianProjectiveMarkedPoint K n h L a ha p q hs i j = 1 ↔ j = i := by
  rw [← completeCartesianProjectiveMarkedPoint_self K n h L a ha p q hs i]
  exact (completeCartesianProjectiveMarkedPoint_injective K n h L a ha p q hs i).eq_iff

end FLT.Mazur.PolygonInfinitesimalStages
