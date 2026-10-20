/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicInitialRoots
public import FLT.Mazur.OneGonAdicSubgroupCartier
public import FLT.Mazur.PolygonPowerSeriesBase

/-!
# Canonical finite subgroups of the genuine complete-base degeneration

The explicit initial roots embedding supplies the input of the adic extension.
This constructs a rank-n subgroup on the nonconstant arithmetic family without
assuming any initial embedding. Over Noetherian coefficients its full ideal is
relative Cartier and ample; cyclicity remains a separate assertion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open ArithmeticOneGonGeneralizedCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- A rank-n subgroup of the original degeneration, with no input subgroup. -/
def canonicalFiniteSubgroup :
    (curve t (complementaryFactor_isUnit I t ht)).FiniteSubgroup n :=
  effectiveFiniteSubgroup I t ht n (initialRootsHom n I t ht)

/-- The constructed subgroup has exact rank n on the entire complete base. -/
theorem canonicalFiniteSubgroup_degree :
    FCurve.FiniteLocallyFreeDegree (canonicalFiniteSubgroup I t ht n).carrier.hom n :=
  (canonicalFiniteSubgroup I t ht n).degree

/-- The full canonical subgroup ideal retains the effective original cubic chart map. -/
theorem canonicalFiniteSubgroup_ideal :
    (canonicalFiniteSubgroup I t ht n).ideal =
      (effectiveAffine I t ht (initialRootsHom n I t ht) ≫
        WeierstrassIntegralChart.integralCurveChart (OneGonSmoothing.equation t) 1).ker :=
  effectiveFiniteSubgroup_ideal I t ht n (initialRootsHom n I t ht)

/-- The full ideal on the original curve is relative Cartier over Noetherian coefficients. -/
theorem canonicalFiniteSubgroup_relativeCartier [IsNoetherianRing R] :
    FCurve.RelativeEffectiveCartier (curve t (complementaryFactor_isUnit I t ht)).curve.hom
      (canonicalFiniteSubgroup I t ht n).ideal :=
  effectiveFiniteSubgroup_relativeCartier I t ht n (initialRootsHom n I t ht)

/-- Its positive-rank divisor is ample on the actual arithmetic degeneration. -/
theorem canonicalFiniteSubgroup_isAmple [IsNoetherianRing R] :
    (canonicalFiniteSubgroup I t ht n).IsAmple :=
  effectiveFiniteSubgroup_isAmple I t ht n (initialRootsHom n I t ht)

/-- A concrete subgroup on the nonconstant mixed-characteristic power-series degeneration. -/
def integralPowerSeriesFiniteSubgroup : integralPowerSeriesCurve.FiniteSubgroup n :=
  canonicalFiniteSubgroup (PolygonInfinitesimalStages.parameterIdeal ℤ) PowerSeries.X
    (Ideal.subset_span (Set.mem_singleton _)) n

/-- The concrete integral degeneration carries a finite locally free subgroup of exact rank n. -/
theorem integralPowerSeriesFiniteSubgroup_degree :
    FCurve.FiniteLocallyFreeDegree (integralPowerSeriesFiniteSubgroup n).carrier.hom n :=
  (integralPowerSeriesFiniteSubgroup n).degree

/-- The actual integral power-series subgroup ideal is relative Cartier. -/
theorem integralPowerSeriesFiniteSubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier integralPowerSeriesCurve.curve.hom
      (integralPowerSeriesFiniteSubgroup n).ideal :=
  canonicalFiniteSubgroup_relativeCartier _ _ _ n

/-- The actual integral power-series subgroup divisor is ample. -/
theorem integralPowerSeriesFiniteSubgroup_isAmple :
    (integralPowerSeriesFiniteSubgroup n).IsAmple :=
  canonicalFiniteSubgroup_isAmple _ _ _ n

end FLT.Mazur.OneGonAdicCharacterTower
