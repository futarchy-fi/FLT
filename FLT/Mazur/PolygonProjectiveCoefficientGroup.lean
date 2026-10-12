/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveCoefficientMap
public import FLT.Mazur.WeierstrassCartesianPullbackGroup

/-!
# The original coefficient comparison preserves the polygon elliptic group

The independently constructed extended-field cubic is compared with the mapped
original equation through their actual pointed isomorphism. Composing with the
coefficient group isomorphism identifies the original monoidal pullback group.
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
local notation "f" => completeProjectiveCoefficientMap K n h L a ha M p q hs r s ht
local notation "hf" => completeProjectiveCoefficientMap_isPullback K n h L a ha M p q hs r s ht
local notation "hz" => completeProjectiveCoefficientMap_zero K n h L a ha M p q hs r s ht

/-- The mapped original equation and independently chosen equation are actually isomorphic. -/
def completeProjectiveCoefficientIso (i : Fin n) :
    integralCurve ((W i).map (algebraMap L M)) ≅ integralCurve (V i) :=
  cartesianCoefficientIso (W i) (V i) (f i) (hf i)

/-- The pointed comparison is over the original extended field. -/
@[reassoc] theorem completeProjectiveCoefficientIso_over (i : Fin n) :
    (completeProjectiveCoefficientIso K n h L a ha M p q hs r s ht i).hom ≫
      integralCurveStructure (V i) = integralCurveStructure ((W i).map (algebraMap L M)) :=
  cartesianCoefficientIso_over (W i) (V i) (f i) (hf i)

/-- The comparison retains the original infinity label. -/
@[reassoc] theorem completeProjectiveCoefficientIso_zero (i : Fin n) :
    integralCurveZero ((W i).map (algebraMap L M)) ≫
      (completeProjectiveCoefficientIso K n h L a ha M p q hs r s ht i).hom =
        integralCurveZero (V i) :=
  cartesianCoefficientIso_zero (W i) (V i) (f i) (hf i) (hz i)

/-- The original elliptic group commutes with this specified coefficient extension. -/
irreducible_def completeProjectiveCoefficientGroupIso (i : Fin n) :
    (Over.pullback b).mapCommGrp.obj (completeProjectiveGroup K n h L a ha p q hs i) ≅
      completeProjectiveGroup K n h M aM haM r s ht i :=
  cartesianPullbackGroupIso (W i) (V i) (f i) (hf i) (hz i) _ _

/-- The group comparison projects to the original morphism between the chosen cubic models. -/
@[reassoc] theorem completeProjectiveCoefficientGroupIso_inv_fst (i : Fin n) :
    (completeProjectiveCoefficientGroupIso K n h L a ha M p q hs r s ht i).inv.hom.hom.hom.left ≫
      CategoryTheory.Limits.pullback.fst (integralCurveStructure (W i)) b = f i := by
  rw [completeProjectiveCoefficientGroupIso_def]
  exact cartesianPullbackGroupIso_inv_fst (W i) (V i) (f i) (hf i) (hz i) _ _

end FLT.Mazur.PolygonInfinitesimalStages
