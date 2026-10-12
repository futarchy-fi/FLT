/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCartesianBaseMap
public import FLT.Mazur.PolygonProjectiveSquareComparison

/-!
# Coefficient maps between the original chosen polygon cubics

Conjugating the actual map of original cartesian squares by the two constructed
projective isomorphisms gives a cartesian map of their independently chosen
cubics. All labels, including the chosen infinity, are retained.
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
  (M : Type) [Field M] [Algebra L M]
  {Y Z : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "eY" => completeCartesianPointProjectiveIso K n h L a ha p q hs
local notation "eZ" => completeCartesianPointProjectiveIso K n h M aM haM r s ht
local notation "W" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) p q hs
local notation "V" => completeCartesianPointWeierstrass K n h M
  (Spec.map (CommRingCat.ofHom aM)) r s ht
/-- The specified original coefficient map commutes with the spectrum base morphism. -/
theorem completeCoefficientSpec_comp :
    b ≫ Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom aM) := by
  rw [← Spec.map_comp]
  rfl

local notation "u" => completeCartesianBaseMap K n h
  (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom aM)) p q hs r s ht b
  (completeCoefficientSpec_comp K L a M)

/-- The actual original coefficient comparison in the two chosen cubic coordinates. -/
def completeProjectiveCoefficientMap (i : Fin n) : integralCurve (V i) ⟶ integralCurve (W i) :=
  (eZ i).inv ≫ u ≫ (eY i).hom

/-- The comparison lies over the original coefficient extension. -/
@[reassoc] theorem completeProjectiveCoefficientMap_over (i : Fin n) :
    completeProjectiveCoefficientMap K n h L a ha M p q hs r s ht i ≫
      integralCurveStructure (W i) = integralCurveStructure (V i) ≫ b := by
  change (eZ i).inv ≫ u ≫ (eY i).hom ≫ _ = _
  rw [completeCartesianPointProjectiveIso_over, completeCartesianBaseMap_snd]
  rw [← Category.assoc]
  congr 1
  exact (congrArg (fun k ↦ (eZ i).inv ≫ k)
    (completeCartesianPointProjectiveIso_over K n h M aM haM r s ht i).symm).trans
      ((eZ i).inv_hom_id_assoc _)

/-- The coefficient comparison is cartesian, with neither chosen equation identified by fiat. -/
theorem completeProjectiveCoefficientMap_isPullback (i : Fin n) :
    IsPullback (completeProjectiveCoefficientMap K n h L a ha M p q hs r s ht i)
      (integralCurveStructure (V i)) (integralCurveStructure (W i)) b := by
  refine (completeCartesianBaseMap_isPullback K n h _ _ p q hs r s ht b
    (by rw [← Spec.map_comp]; rfl)).of_iso (eZ i) (eY i) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
  · change u ≫ (eY i).hom = (eZ i).hom ≫ (eZ i).inv ≫ u ≫ (eY i).hom
    rw [(eZ i).hom_inv_id_assoc]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (completeCartesianPointProjectiveIso_over K n h M aM haM r s ht i).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (completeCartesianPointProjectiveIso_over K n h L a ha p q hs i).symm
  · simp

/-- Every original label survives the coefficient comparison. -/
@[reassoc] theorem completeProjectiveCoefficientMap_marking (i j : Fin n) :
    completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom aM)) r s ht j ≫
      (eZ i).hom ≫ completeProjectiveCoefficientMap K n h L a ha M p q hs r s ht i =
        b ≫ completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs j ≫
          (eY i).hom := by
  change _ ≫ (eZ i).hom ≫ (eZ i).inv ≫ u ≫ (eY i).hom = _
  rw [(eZ i).hom_inv_id_assoc, ← Category.assoc, completeCartesianBaseMap_marking,
    Category.assoc]

/-- In particular the coefficient comparison preserves the original infinity. -/
@[reassoc] theorem completeProjectiveCoefficientMap_zero (i : Fin n) :
    integralCurveZero (V i) ≫
      completeProjectiveCoefficientMap K n h L a ha M p q hs r s ht i =
        b ≫ integralCurveZero (W i) := by
  rw [← completeCartesianPointToProjective_marking K n h M aM haM r s ht i,
    Category.assoc]
  exact (completeProjectiveCoefficientMap_marking K n h L a ha M p q hs r s ht i i).trans
    (congrArg (fun k ↦ b ≫ k)
      (completeCartesianPointToProjective_marking K n h L a ha p q hs i))

end FLT.Mazur.PolygonInfinitesimalStages
