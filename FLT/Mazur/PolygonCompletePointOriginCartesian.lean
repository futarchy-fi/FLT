/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginIdealEquality

/-!
# The original marking is the Cartesian inverse image of the cubic origin

Full ideal equality gives the original marked-point square, including its
scheme structure. All powers retain the original marking ideal as well.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i

local notation "J" => completePointPulledOriginIdeal K n h i

/-- Every power of the original origin ideal pulls back to the original marking power. -/
theorem completePointToIntegralCubic_origin_power (m : ℕ) :
    ((integralCurveZero (W)).ker ^ m).comap (g) = (s).ker ^ m := by
  rw [idealSheaf_comap_pow]
  exact congrArg (fun I => I ^ m) (completePointPulledOriginIdeal_eq_marking K n h i)

/-- The actual original marking square over the original cubic origin is Cartesian. -/
theorem completePointToIntegralCubic_origin_isPullback :
    IsPullback (s) (Spec (.of (PowerSeries K))).toSpecΓ (g) (integralCurveZero (W)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := isClosedImmersion_section (exactVeroneseProjToBase K n h)
    (s) (completeBaseMarking_toBase K n h i)
  exact isPullback_of_isClosedImmersion (s) (integralCurveZero (W))
    (Spec (.of (PowerSeries K))).toSpecΓ (g)
    (completePointToIntegralCubic_marking K n h i)
    (completePointPulledOriginIdeal_eq_marking K n h i)

/-- The entire retained parameter-neighborhood marking square is Cartesian as well. -/
theorem completePointToOrigin_marking_isPullback :
    IsPullback (completePointMarkingOrigin K n h i)
      (Spec (.of (PowerSeries K))).toSpecΓ (q) (originNeighborhoodSection (W)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  have : IsClosedImmersion ((completePointMarkingOrigin K n h i) ≫ (V).ι) := by
    rw [completePointMarkingOrigin_inclusion]
    exact isClosedImmersion_section _ _ (completeBaseMarking_toBase K n h i)
  let _ := IsClosedImmersion.of_comp (completePointMarkingOrigin K n h i) (V).ι
  have he : (originNeighborhoodSection (W)).ker.comap (q) =
      (completePointMarkingOrigin K n h i).ker := by
    rw [← completePointPulledOriginIdeal_neighborhood,
      completePointPulledOriginIdeal_eq_marking, completePointMarkingIdeal_neighborhood]
  exact isPullback_of_isClosedImmersion _ _ _ _
    (completePointMarkingOrigin_toOrigin K n h i) he

end FLT.Mazur.PolygonInfinitesimalStages
