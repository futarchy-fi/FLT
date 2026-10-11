/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedPointLineComparison
public import FLT.Mazur.PolygonCompleteCartesianPointCohomology
public import FLT.Mazur.PolygonSinglePointPowerNormalization

/-!
# Powers of the original complete point line on the closed and general fibers

The tensor-power comparison identifies the original complete coefficient with
the actual labeled point power. On the closed polygon it lands in the very
ideal-power sheaf used in the single-point normalization calculation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback PolygonSinglePointLineNormalization

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every original point-line tensor power retains its actual labeled Cartesian coefficient. -/
def completeCartesianPointPowerIso {S Y : Scheme}
    (s : S ⟶ Spec (.of (PowerSeries K))) (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
    (hs : IsPullback p q (exactVeroneseProjToBase K n h) s) (i : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback p).obj (tensorPower (completePointLine K n h i) m) ≅
      tensorPower (completeCartesianPointLine K n h s p q hs i) m :=
  tensorPowerIso p (completePointLine K n h i) m ≪≫
    tensorPowerCongr (completeCartesianPointLineIso K n h s p q hs i) m

/-- The original complete tensor power restricts to the original polygon ideal-power line. -/
def completePointPowerClosedIso (i : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).obj
      (tensorPower (completePointLine K n h i) m) ≅
        pointPower K n (by omega) (PolygonCyclicAtlas.normalization K n h)
          (PolygonCyclicAtlas.nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega))
          1 i m :=
  tensorPowerIso _ (completePointLine K n h i) m ≪≫
    tensorPowerCongr (completePointLineClosedIso K n h i) m ≪≫
      pointPowerIso K n (by omega) _ _ (PolygonCyclicPushout.isPushout K n h (by omega)) 1 i m

variable (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

include hs in
/-- The pullback of the original complete coefficient itself has degree equal to the exponent. -/
theorem completePointPower_pullback_degree (i : Fin n) (m : ℕ) :
    curveSheafDegree q
      ((Scheme.Modules.pullback p).obj (tensorPower (completePointLine K n h i) m)) =
        (m : ℤ) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  rw [curveSheafDegree_iso q (completeCartesianPointPowerIso K n h s p q hs i m)]
  exact completeCartesianPointLine_power_degree K n h L s p q hs i m

include hs in
/-- Actual H0 of the original complete coefficient satisfies the computed two-case bound. -/
theorem completePointPower_pullback_h0_cases (i : Fin n) (m : ℕ) :
    let d := Module.finrank L (ModuleScalarH q
      ((Scheme.Modules.pullback p).obj (tensorPower (completePointLine K n h i) m)) 0)
    d = m ∨ d = m + 1 := by
  dsimp only
  let e : ModuleScalarH q
      ((Scheme.Modules.pullback p).obj (tensorPower (completePointLine K n h i) m)) 0 ≃ₗ[L]
      ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0 :=
    ((moduleScalarHFunctor q 0).mapIso
      (completeCartesianPointPowerIso K n h s p q hs i m)).toLinearEquiv
  rw [e.finrank_eq]
  exact completeCartesianPointLine_power_h0_cases K n h L s p q hs i m

end FLT.Mazur.PolygonInfinitesimalStages
