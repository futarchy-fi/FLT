/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointInfinity

/-!
# The other original markings in the pointed affine cubic

Every label distinct from the retained infinity label lies in its actual
complement. Its resulting monic affine point is constructed over the original
field, and the projective comparison preserves that entire section morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- Every other original section lies in the actual retained-point complement. -/
theorem completeCartesianOtherMarking_range_complement (i j : Fin n) (hij : j ≠ i) :
    Set.range (completeCartesianMarking K n h
      (Spec.map (CommRingCat.ofHom a)) p q hs j) ⊆
      (completeCartesianPointComplement K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i : Set Y) := by
  intro y hy
  change y ∉ ((completeCartesianMarking K n h
    (Spec.map (CommRingCat.ofHom a)) p q hs i).ker.support : Set Y)
  rw [completeCartesianMarking_support]
  exact Set.disjoint_left.mp
    (completeCartesianMarkings_pairwise K n h _ p q hs hij) hy

/-- The actual other labeled section, factored through the original point complement. -/
def completeCartesianOtherMarkingToComplement (i j : Fin n) (hij : j ≠ i) :
    Spec (.of L) ⟶ (completeCartesianPointComplement K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).toScheme :=
  IsOpenImmersion.lift (completeCartesianPointComplement K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i).ι (completeCartesianMarking K n h
    (Spec.map (CommRingCat.ofHom a)) p q hs j) (by
      simpa only [Scheme.Opens.range_ι] using
        completeCartesianOtherMarking_range_complement K n h L a p q hs i j hij)

/-- Factoring the section leaves the original labeled morphism unchanged. -/
theorem completeCartesianOtherMarkingToComplement_ι (i j : Fin n) (hij : j ≠ i) :
    completeCartesianOtherMarkingToComplement K n h L a p q hs i j hij ≫
      (completeCartesianPointComplement K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i).ι =
      completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The other label as a concrete point of the original monic coordinate model. -/
def completeCartesianOtherMarkingAffine (i j : Fin n) (hij : j ≠ i) :
    Spec (.of L) ⟶ Spec (.of (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i).toAffine.CoordinateRing) :=
  completeCartesianOtherMarkingToComplement K n h L a p q hs i j hij ≫
    completeCartesianPointToAffineCubic K n h L _ p q hs i

/-- The constructed affine marking is a point over the unchanged original field. -/
theorem completeCartesianOtherMarkingAffine_over (i j : Fin n) (hij : j ≠ i) :
    completeCartesianOtherMarkingAffine K n h L a p q hs i j hij ≫
      Spec.map (CommRingCat.ofHom (algebraMap L
        (completeCartesianPointWeierstrass K n h L
          (Spec.map (CommRingCat.ofHom a)) p q hs i).toAffine.CoordinateRing)) =
      𝟙 (Spec (.of L)) := by
  rw [completeCartesianOtherMarkingAffine, Category.assoc,
    completeCartesianPointToAffineCubic_over, ← Category.assoc,
    completeCartesianOtherMarkingToComplement_ι, completeCartesianMarking_snd]

/-- Every other marking is preserved by the original projective extension. -/
theorem completeCartesianOtherMarkingAffine_projective (i j : Fin n) (hij : j ≠ i) :
    completeCartesianOtherMarkingAffine K n h L a p q hs i j hij ≫
      monicToIntegralCurve (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) =
      completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs j ≫
        completeCartesianPointToProjective K n h L a ha p q hs i := by
  rw [← completeCartesianOtherMarkingToComplement_ι K n h L a p q hs i j hij,
    Category.assoc, completeCartesianPointToProjective_restrict]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
