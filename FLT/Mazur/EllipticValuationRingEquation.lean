/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ValuationRingModel
public import FLT.Mazur.EllipticGoodReductionDiscriminant

/-!
# The original integral equation in its valuation subring

Realizing the coefficient DVR inside the fraction field changes neither the
generic equation nor the original variable change. In the good-reduction
branch its transported discriminant is a unit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve

variable {S L : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The supplied equation with coefficients in the actual valuation subring. -/
def fractionValuationEquation (U : WeierstrassCurve S) :
    WeierstrassCurve (fractionValuationSubring S L) :=
  U.map (fractionValuationEquiv S L).toRingHom

/-- The generic equation is exactly the original one, not merely isomorphic to it. -/
theorem fractionValuationEquation_generic (U : WeierstrassCurve S) :
    (fractionValuationEquation (L := L) U).map
      (algebraMap (fractionValuationSubring S L) L) = U.map (algebraMap S L) := by
  rw [fractionValuationEquation, map_map]
  rfl

/-- The original variable change remains valid after realizing the integral ring. -/
theorem fractionValuationEquation_variableChange (E : WeierstrassCurve L)
    (U : WeierstrassCurve S) (C : VariableChange L)
    (hC : C • E = U.map (algebraMap S L)) :
    C • E = (fractionValuationEquation (L := L) U).map
      (algebraMap (fractionValuationSubring S L) L) :=
  hC.trans (fractionValuationEquation_generic U).symm

/-- Good reduction of the supplied equation yields a unit transported discriminant. -/
theorem fractionValuationEquation_discriminant_unit (U : WeierstrassCurve S)
    [(U.map (algebraMap S L)).HasGoodReduction S] :
    IsUnit (fractionValuationEquation (L := L) U).Δ := by
  rw [fractionValuationEquation, map_Δ]
  exact (isUnit_discriminant_of_hasGoodReduction (K := L) U).map _

end FLT.Mazur
