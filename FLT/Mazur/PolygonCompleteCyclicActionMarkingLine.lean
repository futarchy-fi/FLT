/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCyclicActionDivisor
public import FLT.Mazur.DivisorLineSectionIdentity
public import FLT.Mazur.DivisorLineSectionTriangle
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Original marking-line comparisons for the cyclic whole action

The full original marked divisor gives a canonical section-preserving line
comparison under each cyclic action. Identity, composition, and every tensor
power retain the actual sheaf pullback unitors and compositors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "r" => completeCyclicActionMap K n h
local notation "L" => completeMarkingLine K n h
local notation "c" => And.left (completeMarkingDivisor_relativeCartier K n h)

/-- The original ideal-module comparison under the cyclic action is invertible. -/
instance completeCyclicActionMarkingIdeal_isIso (b : ZMod n) :
    IsIso (idealModulePullbackHom (completeMarkingDivisor K n h) (r b)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (c)
  rw [completeCyclicActionMap_divisor]
  exact (c)

/-- The actual canonical marking-line comparison for each cyclic whole action. -/
def completeCyclicActionMarkingLineIso (b : ZMod n) :
    (Scheme.Modules.pullback (r b)).obj (L) ≅ (L) :=
  divisorLinePullbackIsoOfEq (r b) (c) (c) (completeCyclicActionMap_divisor K n h b)

/-- The original marking section, including its multiplicities, is preserved. -/
theorem completeCyclicActionMarkingLineIso_section (b : ZMod n) :
    DivisorLineSectionCompatible (r b) (c) (c) (completeCyclicActionMarkingLineIso K n h b) :=
  divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The zero-label line comparison is exactly the original pullback identity comparison. -/
theorem completeCyclicActionMarkingLineIso_zero :
    completeCyclicActionMarkingLineIso K n h 0 =
      (Scheme.Modules.pullbackCongr (completeCyclicActionMap_zero K n h)).app (L) ≪≫
        (Scheme.Modules.pullbackId _).app (L) :=
  (completeCyclicActionMarkingLineIso_section K n h 0).eq_id
    (completeCyclicActionMap_zero K n h)

/-- Cyclic composition satisfies the actual original marking-line cocycle. -/
theorem completeCyclicActionMarkingLineIso_cocycle (b d : ZMod n) :
    LinePullbackTriangle (r b) (r d) (r (b + d)) (completeCyclicActionMap_add K n h b d)
      (completeCyclicActionMarkingLineIso K n h d)
      (completeCyclicActionMarkingLineIso K n h b)
      (completeCyclicActionMarkingLineIso K n h (b + d)) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeCyclicActionMarkingLineIso_section K n h d)
    (completeCyclicActionMarkingLineIso_section K n h b)
    (completeCyclicActionMarkingLineIso_section K n h (b + d))

/-- Every tensor degree retains the same original line cocycle. -/
theorem completeCyclicActionMarkingLineIso_power_cocycle (b d : ZMod n) (m : ℕ) :
    LinePullbackTriangle (r b) (r d) (r (b + d)) (completeCyclicActionMap_add K n h b d)
      (tensorPowerPullbackComparison _ (completeCyclicActionMarkingLineIso K n h d) m)
      (tensorPowerPullbackComparison _ (completeCyclicActionMarkingLineIso K n h b) m)
      (tensorPowerPullbackComparison _ (completeCyclicActionMarkingLineIso K n h (b + d)) m) :=
  (completeCyclicActionMarkingLineIso_cocycle K n h b d).tensorPower m

/-- Every powered comparison preserves the original powered marking section. -/
theorem completeCyclicActionMarkingLineIso_power_section (b : ZMod n) (m : ℕ) :
    DivisorLinePowerSectionCompatible (r b) (c) (c)
      (completeCyclicActionMarkingLineIso K n h b) m :=
  (completeCyclicActionMarkingLineIso_section K n h b).tensorPower_section m

end FLT.Mazur.PolygonInfinitesimalStages
