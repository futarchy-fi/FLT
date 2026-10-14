/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginCartesian
public import FLT.Mazur.PolygonCompleteCartesianPointDivisor

/-!
# The original origin comparison on every retained Cartesian family

The full origin ideal and its powers pull back to each specified original marking.
The original marked-point square remains Cartesian on singular fibers too.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

variable (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "t" => completeCartesianMarking K n h s p q hs i

/-- The actual original cubic-origin ideal pulls back to the retained single marking. -/
theorem completeCartesianPointToOriginalCubic_originIdeal :
    (integralCurveZero (W)).ker.comap (p ≫ (g)) = (t).ker := by
  rw [Scheme.IdealSheafData.comap_comp]
  change (completePointPulledOriginIdeal K n h i).comap p = _
  rw [completePointPulledOriginIdeal_eq_marking, completeCartesianMarking_ker]

/-- Every powered origin ideal retains its original single-point multiplicity after base change. -/
theorem completeCartesianPointToOriginalCubic_originPower (m : ℕ) :
    ((integralCurveZero (W)).ker ^ m).comap (p ≫ (g)) = (t).ker ^ m := by
  rw [idealSheaf_comap_pow, completeCartesianPointToOriginalCubic_originIdeal]

/-- The comparison retains the actual marking and the actual coefficient-base map. -/
@[reassoc] theorem completeCartesianPointToOriginalCubic_marking :
    (t) ≫ p ≫ (g) =
      (s ≫ (Spec (.of (PowerSeries K))).toSpecΓ) ≫ integralCurveZero (W) := by
  rw [← Category.assoc, completeCartesianMarking_fst, Category.assoc,
    completePointToIntegralCubic_marking, Category.assoc]

/-- The original single-point Cartesian square survives every specified family square. -/
theorem completeCartesianPointToOriginalCubic_origin_isPullback :
    IsPullback (t) (s ≫ (Spec (.of (PowerSeries K))).toSpecΓ)
      (p ≫ (g)) (integralCurveZero (W)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ := isClosedImmersion_section q (t) (completeCartesianMarking_snd K n h s p q hs i)
  exact isPullback_of_isClosedImmersion _ _ _ _
    (completeCartesianPointToOriginalCubic_marking K n h s p q hs i)
    (completeCartesianPointToOriginalCubic_originIdeal K n h s p q hs i)

end FLT.Mazur.PolygonInfinitesimalStages
