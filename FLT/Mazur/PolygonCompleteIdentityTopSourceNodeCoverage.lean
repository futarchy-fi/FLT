/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopSourcePoleMaps
public import FLT.Mazur.PolygonSmoothingNodeDenominatorCoverage

/-!
# The actual source-node locus survives reciprocal scaling and pole localization

The independent Laurent scaling factors are units in the unchanged affine
patch. Thus source coordinate ideals and source node primes are unchanged,
and every such prime belongs to the actual scaled source denominator open.
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
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "A" => Γ((R), (V).1)
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
local notation "a" => RingHom.comp (CommRingCat.Hom.hom (ρ))
  (completeIdentityTopAmbientSourceFunctions K n h m)
local notation "s" => completeIdentityTopPoleSource K n h m U
local notation "u" => parameterUnit K (m + 1)
local notation "η" => algebraMap (Ring K[T;T⁻¹] (m + 1)) (ChartRing (e))

/-- The actual outgoing scaled source is its original coordinate times the original unit. -/
theorem completeIdentityTopPoleSource_left :
    (s) (leftCoordinate (t)) = (a) ((η) (u)) * (a) (leftCoordinate (e)) := by
  change (a) ((reciprocalScale (e) (u))
    (ringMap _ (t) (e) (stageCoefficientMap_parameter _ _) (leftCoordinate (t)))) = _
  rw [ringMap_left, reciprocalScale_left, (a).map_mul]

/-- The actual incoming scaled source retains the inverse of that same unit. -/
theorem completeIdentityTopPoleSource_right :
    (s) (rightCoordinate (t)) = (a) ((η) (↑(u)⁻¹)) * (a) (rightCoordinate (e)) := by
  change (a) ((reciprocalScale (e) (u))
    (ringMap _ (t) (e) (stageCoefficientMap_parameter _ _) (rightCoordinate (t)))) = _
  rw [ringMap_right, reciprocalScale_right, (a).map_mul]

/-- Reciprocal scaling preserves membership of the outgoing source coordinate in every ideal. -/
theorem completeIdentityTopPoleSource_left_mem_iff (I : Ideal (A)) :
    (s) (leftCoordinate (t)) ∈ I ↔ (a) (leftCoordinate (e)) ∈ I := by
  rw [completeIdentityTopPoleSource_left]
  exact I.unit_mul_mem_iff_mem (((u).isUnit.map (η)).map (a))

/-- The same equivalence holds for the incoming coordinate and the full original ideal. -/
theorem completeIdentityTopPoleSource_right_mem_iff (I : Ideal (A)) :
    (s) (rightCoordinate (t)) ∈ I ↔ (a) (rightCoordinate (e)) ∈ I := by
  rw [completeIdentityTopPoleSource_right]
  exact I.unit_mul_mem_iff_mem ((((u)⁻¹).isUnit.map (η)).map (a))

/-- The source marking denominator misses every prime in the original full source-node locus. -/
theorem completeIdentityTopPoleSource_node_coverage (p : PrimeSpectrum (A))
    (hx : (a) (leftCoordinate (e)) ∈ p.asIdeal)
    (hy : (a) (rightCoordinate (e)) ∈ p.asIdeal) :
    (s) (nodeMarkingDenominator (t)) ∉ p.asIdeal :=
  nodeMarkingDenominator_not_mem (t) (s) p.asIdeal p.isPrime.ne_top
    ((completeIdentityTopPoleSource_left_mem_iff K n h m U p.asIdeal).mpr hx)
    ((completeIdentityTopPoleSource_right_mem_iff K n h m U p.asIdeal).mpr hy)

end FLT.Mazur.PolygonInfinitesimalStages
