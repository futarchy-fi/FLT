/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopAmbientNodeGenerators
public import FLT.Mazur.PolygonCompleteIdentityFirstPositiveLaw

/-!
# The actual second-stage socle has two original error generators

The proved first positive law discharges the preceding-law hypothesis.
Every common annihilator in the full second ambient chart belongs to the
parameter-plus-two-errors ideal. Local vanishing of those errors remains.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The already proved original first positive law has zero literal multiplication defect. -/
theorem completeIdentitySecondPrecedingDefect : completeIdentityFiniteMulDefect K n h 0 1 = 0 :=
  (completeIdentityFiniteLaw_iff_defect K n h 0 1).mp
    (completeIdentityFiniteLaw_firstPositive K n h)

local notation "R" => completeIdentityActionAdicChartSpace K n h 2 0 0
local notation "t" => parameter K 2
local notation "e" => parameter K[T;T⁻¹] 2
local notation "s" => completeIdentityTopAmbientSourceFunctions K n h 1
local notation "J" => completeIdentityTopChartClosedAmbientIdeal K n h 1
local notation "δ" => completeIdentityTopAmbientError K n h 1

/-- Every actual second-stage socle representative is a parameter-plus-two-errors relation. -/
theorem completeIdentitySecondAmbientSocle_twoErrors (z : Γ((R), ⊤))
    (hx : (s) (leftCoordinate (e)) * z ∈ (J))
    (hy : (s) (rightCoordinate (e)) * z ∈ (J)) :
    z ∈ Ideal.span {completeIdentityTopAmbientParameter K n h 1} ⊔
      Ideal.span {(δ) (leftCoordinate (t)), (δ) (rightCoordinate (t))} := by
  rw [← completeIdentityTopAmbientNodeKernel_twoCoordinates K n h 1
    (completeIdentitySecondPrecedingDefect K n h)]
  exact completeIdentityTopChartAmbientSocle_nodeKernel K n h 1
    (completeIdentitySecondPrecedingDefect K n h) z hx hy

end FLT.Mazur.PolygonInfinitesimalStages
