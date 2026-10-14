/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointRelativeAffinization
public import FLT.Mazur.PolygonCompletePointRelativeAffineRestriction

/-!
# The original global cubic map is an affinization on its Z chart
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "U" => GlobalIdealPowerCompatibility.complement (Scheme.Hom.ker (s))
local notation "W" => completePointWeierstrassCurve K n h i

/-- The original monic chart comparison as an actual scheme isomorphism. -/
def completePointMonicChartIso :
    Spec (.of (W).toAffine.CoordinateRing) ≅ Spec (.of (Coordinate (W) 2)) := by
  let _ : IsIso (CommRingCat.ofHom (affineChartToMonic (W)).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (affineChartMonicEquiv (W)).bijective
  exact asIso (Spec.map (CommRingCat.ofHom (affineChartToMonic (W)).toRingHom))

/-- The original global cubic map on the actual marking complement, valued in its Z chart. -/
def completePointComplementToCubicChart : (U).toScheme ⟶ Spec (.of (Coordinate (W) 2)) :=
  completePointToAffineCubic K n h i ≫ (completePointMonicChartIso K n h i).hom

/-- The chart-valued affinization retains the original global complete-base contraction. -/
@[reassoc] theorem completePointComplementToCubicChart_inclusion :
    completePointComplementToCubicChart K n h i ≫ integralCurveChart (W) 2 =
      (U).ι ≫ completePointToIntegralCubic K n h i := by
  change (completePointToAffineCubic K n h i ≫
    Spec.map (CommRingCat.ofHom (affineChartToMonic (W)).toRingHom)) ≫
      integralCurveChart (W) 2 = _
  rw [Category.assoc]
  exact (completePointToIntegralCubic_affine K n h i).symm

/-- Every affine-valued map factors uniquely through this original global contraction chart. -/
theorem completePointComplementToCubicChart_existsUnique_factor
    (T : Scheme) [IsAffine T] (q : (U).toScheme ⟶ T) :
    ∃! b : Spec (.of (Coordinate (W) 2)) ⟶ T,
      completePointComplementToCubicChart K n h i ≫ b = q := by
  let e := completePointMonicChartIso K n h i
  obtain ⟨b, hb, hu⟩ := completePointToAffineCubic_existsUnique_factor K n h i T q
  refine ⟨e.inv ≫ b, ?_, ?_⟩
  · change (completePointToAffineCubic K n h i ≫ e.hom) ≫ (e.inv ≫ b) = q
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hb
  · intro d hd
    have he : e.hom ≫ d = b := hu _ (by
      dsimp only
      rw [← Category.assoc]
      exact hd)
    rw [← he, Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
