/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartResidualPresentation
public import FLT.Mazur.PolygonCompleteIdentityTopChartAmbientErrors
public import FLT.Mazur.PolygonCompleteIdentityTopChartAmbientSocle

/-!
# Higher ambient target reduction and residual node socle

The actual target reduces to source scaling on the split node. Every
ambient common annihilator lies in the full residual kernel. Neither
statement asserts that the residual ideal vanishes in the original fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField completeIdentityTopGraphReduction
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (hm : completeIdentityFiniteMulDefect K n h 0 m = 0)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "B" => ChartRing (t)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0
local notation "v" => completeIdentityTopGraphToChart K n h m
local notation "s" => completeIdentityTopAmbientSourceFunctions K n h m
local notation "p" => completeIdentityTopAmbientTargetFunctions K n h m
local notation "q" => completeIdentityTopChartTargetFunctions K n h m
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K (m + 1))
local notation "f" => completeIdentityTopChartClosedAmbientMap K n h m
local notation "J" => completeIdentityTopChartClosedAmbientIdeal K n h m

/-- The actual target reduces to reciprocal scaling on the unchanged source node. -/
theorem completeIdentityTopAmbientNodeReduction_target (z : B) :
    completeIdentityTopAmbientNodeReduction K n h m hm ((p) z) =
      topNodeReduction K[T;T⁻¹] m ((σ) ((b) z)) := by
  change completeIdentityTopChartNodeReduction K n h m hm ((c).appTop ((p) z)) = _
  rw [completeIdentityTopAmbientTargetFunctions_restrict]
  change completeIdentityTopGraphReduction K n h 0 m hm
    (SpectrumGlobalRange.ringHom (v) ((q) z)) = _
  rw [completeIdentityTopChartTargetFunctions_evaluation,
    completeIdentityTopGraphReduction_target]

/-- Every full ambient common annihilator belongs to the original residual node kernel. -/
theorem completeIdentityTopChartAmbientSocle_nodeKernel (z : Γ((R), ⊤))
    (hx : (s) (leftCoordinate (e)) * z ∈ (J))
    (hy : (s) (rightCoordinate (e)) * z ∈ (J)) :
    completeIdentityTopAmbientNodeReduction K n h m hm z = 0 :=
  completeIdentityTopChartClosedSocle_reduction K n h m hm ((f) z)
    ((completeIdentityTopChartAmbientSocle_left K n h m z).mpr hx)
    ((completeIdentityTopChartAmbientSocle_right K n h m z).mpr hy)

end FLT.Mazur.PolygonInfinitesimalStages
