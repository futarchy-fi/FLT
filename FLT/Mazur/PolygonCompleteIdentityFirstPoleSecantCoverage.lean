/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PairedAwayLocalizationSpectrum
public import FLT.Mazur.PolygonSmoothingNodeDenominatorCoverage
public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchCancellation

/-!
# Actual pole and secant neighborhoods over original node primes

Both localizations retain every original patch prime where the two marking
denominators are nonzero and the scaled source outgoing coordinate vanishes.
In particular this covers the simultaneous source and target coordinate-node
locus. This does not identify that locus with the full residual source locus.
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

/-- The actual secant patch covers each original source-node prime in both denominator opens. -/
theorem completeIdentityFirstPoleSecant_exists_prime (p : PrimeSpectrum (A))
    (hq : (q) (d) ∉ p.asIdeal) (hs : (s) (d) ∉ p.asIdeal)
    (hx : (s) (x) ∈ p.asIdeal) :
    ∃ r : PrimeSpectrum (T), PrimeSpectrum.comap ((ν).comp (ι)) r = p := by
  apply PairedAwayLocalization.exists_prime_over_away (q) (s) (d) p hq hs
  intro r hr
  apply completeIdentityFirstPolePatch_coefficient_not_mem K n h U r.asIdeal r.isPrime.ne_top
  rw [completeIdentityFirstPoleSourceMap_algebraMap]
  change (s) (x) ∈ (PrimeSpectrum.comap (ι) r).asIdeal
  rwa [hr]

/-- Both marking localizations and the secant localization cover every original node pair. -/
theorem completeIdentityFirstPoleSecant_nodePair_coverage (p : PrimeSpectrum (A))
    (hqx : (q) (x) ∈ p.asIdeal) (hqy : (q) (y) ∈ p.asIdeal)
    (hsx : (s) (x) ∈ p.asIdeal) (hsy : (s) (y) ∈ p.asIdeal) :
    ∃ r : PrimeSpectrum (T), PrimeSpectrum.comap ((ν).comp (ι)) r = p :=
  completeIdentityFirstPoleSecant_exists_prime K n h U p
    (nodeMarkingDenominator_not_mem (t) (q) p.asIdeal p.isPrime.ne_top hqx hqy)
    (nodeMarkingDenominator_not_mem (t) (s) p.asIdeal p.isPrime.ne_top hsx hsy) hsx

end FLT.Mazur.PolygonInfinitesimalStages
