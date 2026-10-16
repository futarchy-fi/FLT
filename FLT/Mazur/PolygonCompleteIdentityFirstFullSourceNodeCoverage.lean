/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPoleSecantCoverage
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceNodeIncomingIdeals
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceNodeOutgoingIdeals

/-!
# The actual secant patch covers the entire original graph source-node locus

The original full-graph ideal supplies both target node coordinates at
all source-node primes. Thus the existing paired denominator and secant
localizations lose no point of that locus. No radical replaces the graph.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "A" => Γ((R), (V).1)
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "T" => CompleteIdentityFirstPoleSecantPatch K n h U
local notation "ι" => algebraMap (A) (Z)
local notation "ν" => algebraMap (Z) (T)
local notation "q" => completeIdentityFirstPoleTarget K n h U
local notation "s" => completeIdentityFirstPoleSource K n h U
local notation "d" => nodeMarkingDenominator (t)
local notation "x" => leftCoordinate (t)
local notation "y" => rightCoordinate (t)

/-- Every original full-graph source-node prime lifts to the actual secant patch. -/
theorem completeIdentityFirstPoleSecant_fullSourceNode_coverage (p : PrimeSpectrum (A))
    (hI : (completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).ker.ideal
      (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U) ≤ p.asIdeal)
    (hx : completeIdentityFirstPoleSource K n h U
      (leftCoordinate (parameter K 1)) ∈ p.asIdeal)
    (hy : completeIdentityFirstPoleSource K n h U
      (rightCoordinate (parameter K 1)) ∈ p.asIdeal) :
    ∃ r : PrimeSpectrum (T), PrimeSpectrum.comap ((ν).comp (ι)) r = p := by
  exact completeIdentityFirstPoleSecant_nodePair_coverage K n h U p
    (completeIdentityFirstSourceNode_target_mem K n h U p.asIdeal hx hy)
    (completeIdentityFirstSourceNode_incoming_target_mem K n h U p.asIdeal hx hy hI) hx hy

end FLT.Mazur.PolygonInfinitesimalStages
