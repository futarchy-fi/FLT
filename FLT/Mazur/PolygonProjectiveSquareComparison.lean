/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveAuxiliaryMarking
public import FLT.Mazur.PolygonCompleteMarkingNaturality
public import FLT.Mazur.WeierstrassOriginIsomorphismGroup

/-!
# Independence of the chosen cartesian realization of a smooth polygon fiber

The actual comparison of the original cartesian squares induces a pointed
isomorphism of their constructed cubics. It retains every original marking
and upgrades to an isomorphism of the original elliptic group objects.
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
  {Y Z : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of L))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "W" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) p q hs
local notation "V" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) r s ht
local notation "eY" => completeCartesianPointProjectiveIso K n h L a ha p q hs
local notation "eZ" => completeCartesianPointProjectiveIso K n h L a ha r s ht

/-- The actual square comparison transported through the two original projective isomorphisms. -/
def completeProjectiveSquareIso (i : Fin n) : integralCurve (W i) ≅ integralCurve (V i) :=
  (eY i).symm ≪≫ hs.isoIsPullback _ _ ht ≪≫ eZ i

/-- The transported comparison is over the unchanged original coefficient field. -/
@[reassoc] theorem completeProjectiveSquareIso_over (i : Fin n) :
    (completeProjectiveSquareIso K n h L a ha p q hs r s ht i).hom ≫
      integralCurveStructure (V i) = integralCurveStructure (W i) := by
  change (eY i).inv ≫ (hs.isoIsPullback _ _ ht).hom ≫ (eZ i).hom ≫ _ = _
  rw [completeCartesianPointProjectiveIso_over, hs.isoIsPullback_hom_snd]
  exact (congrArg (fun k ↦ (eY i).inv ≫ k)
    (completeCartesianPointProjectiveIso_over K n h L a ha p q hs i).symm).trans
      ((eY i).inv_hom_id_assoc _)

/-- Every retained original label survives the actual square comparison. -/
@[reassoc] theorem completeProjectiveSquareIso_marking (i j : Fin n) :
    completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs j ≫
      (eY i).hom ≫ (completeProjectiveSquareIso K n h L a ha p q hs r s ht i).hom =
        completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) r s ht j ≫
          (eZ i).hom := by
  change _ ≫ (eY i).hom ≫ (eY i).inv ≫ (hs.isoIsPullback _ _ ht).hom ≫ (eZ i).hom = _
  rw [(eY i).hom_inv_id_assoc, ← Category.assoc,
    completeCartesianMarking_isoIsPullback]

/-- In particular the original chosen infinity is retained. -/
@[reassoc] theorem completeProjectiveSquareIso_zero (i : Fin n) :
    integralCurveZero (W i) ≫
      (completeProjectiveSquareIso K n h L a ha p q hs r s ht i).hom =
        integralCurveZero (V i) := by
  rw [← completeCartesianPointToProjective_marking K n h L a ha p q hs i,
    Category.assoc]
  exact (completeProjectiveSquareIso_marking K n h L a ha p q hs r s ht i i).trans
    (completeCartesianPointToProjective_marking K n h L a ha r s ht i)

/-- The original square comparison itself preserves the two constructed elliptic group laws. -/
def completeProjectiveSquareGroupIso (i : Fin n) :
    completeProjectiveGroup K n h L a ha p q hs i ≅
      completeProjectiveGroup K n h L a ha r s ht i :=
  originIsoGroupIso (W i) (V i) _ _
    (completeProjectiveSquareIso K n h L a ha p q hs r s ht i)
    (completeProjectiveSquareIso_over K n h L a ha p q hs r s ht i)
    (completeProjectiveSquareIso_zero K n h L a ha p q hs r s ht i)

/-- The group upgrade retains exactly the original projective comparison morphism. -/
theorem completeProjectiveSquareGroupIso_hom (i : Fin n) :
    (completeProjectiveSquareGroupIso K n h L a ha p q hs r s ht i).hom.hom.hom.hom.left =
      (completeProjectiveSquareIso K n h L a ha p q hs r s ht i).hom := rfl

end FLT.Mazur.PolygonInfinitesimalStages
