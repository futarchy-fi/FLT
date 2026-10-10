/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ValuationRingModel
public import FLT.Mazur.HenselianRingEquivalence
public import FLT.GroupScheme.LocalPolynomialObstruction
public import FLT.GroupScheme.RaynaudFiniteValuation

/-!
# Henselianity and absolute order in the realized valuation ring

The canonical realization preserves the residue field and the order of every
element. In particular, the small absolute ramification bound from a complete
semistable extension remains valid in the actual valuation subring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open IsLocalRing IsDiscreteValuationRing

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

local instance : IsDiscreteValuationRing (fractionValuationSubring R K) :=
  fractionValuationSubring_isDiscreteValuationRing R K

/-- Root lifting survives realization of the DVR in its fraction field. -/
theorem fractionValuationSubring_henselian [HenselianLocalRing R] :
    HenselianLocalRing (fractionValuationSubring R K) :=
  henselianLocalRing_of_ringEquiv (fractionValuationEquiv R K)

/-- The canonical realization has the same residue field. -/
def fractionValuationResidueEquiv :
    ResidueField R ≃+* ResidueField (fractionValuationSubring R K) :=
  ResidueField.mapEquiv (fractionValuationEquiv R K)

/-- Residue characteristic is unchanged by realization. -/
theorem fractionValuationSubring_residue_char (p : ℕ) [CharP (ResidueField R) p] :
    CharP (ResidueField (fractionValuationSubring R K)) p :=
  charP_of_injective_ringHom (f := (fractionValuationResidueEquiv R K).toRingHom)
    (fractionValuationResidueEquiv R K).injective p

/-- Finite residue fields remain finite under realization. -/
theorem fractionValuationSubring_residue_finite [Finite (ResidueField R)] :
    Finite (ResidueField (fractionValuationSubring R K)) :=
  Finite.of_equiv _ (fractionValuationResidueEquiv R K).toEquiv

/-- The actual absolute order of every integral element is preserved. -/
theorem fractionValuationEquiv_order (x : R) :
    RaynaudParameters.order (fractionValuationEquiv R K x) = RaynaudParameters.order x :=
  congrArg ENat.toNat (addValRingEquiv (fractionValuationEquiv R K) x)

/-- The absolute order of the residue prime is unchanged. -/
theorem fractionValuationSubring_prime_order (p : ℕ) :
    RaynaudParameters.order (p : fractionValuationSubring R K) =
      RaynaudParameters.order (p : R) := by
  simpa only [map_natCast] using fractionValuationEquiv_order R K (p : R)

end FLT.Mazur
