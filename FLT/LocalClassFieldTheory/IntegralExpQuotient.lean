/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicIntegerCompact
public import FLT.LocalClassFieldTheory.AcyclicOpenUnits
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The finite integral-unit quotient by the exponential lattice

Pull the constructed open field-unit subgroup back to the integral units.
The integer topology is compact, so this actual quotient is finite.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- The actual integral units whose images belong to the exponential lattice. -/
def integralExpUnits : Subgroup Sˣ :=
  (normalLatticeExpUnits R S K L p).comap (Units.map (algebraMap S L))

/-- Pulling back the proved open subgroup gives an open integral-unit subgroup. -/
theorem integralExpUnits_isOpen :
    letI := dvrIntegerUniformity S L
    IsOpen (integralExpUnits R S K L p : Set Sˣ) := by
  let := dvrAdicValued S L
  let := dvrIntegerUniformity S L
  have hc : Continuous (algebraMap S L) := continuous_induced_dom
  exact (normalLatticeExpUnits_isOpen R S K L p).preimage
    (hc.units_map (algebraMap S L).toMonoidHom)

/-- The integral-unit quotient is finite, derived from compactness and openness. -/
theorem integralExpUnits_quotient_finite [Finite (ResidueField S)] :
    Finite (Sˣ ⧸ integralExpUnits R S K L p) := by
  let := dvrIntegerUniformity S L
  let : CompactSpace S := instAdicIntegerCompactSpace S L
  let : T2Space S := instAdicIntegerT2Space S L
  let : IsTopologicalRing S := instAdicIntegerTopologicalRing S L
  exact Subgroup.quotient_finite_of_isOpen (integralExpUnits R S K L p)
    (integralExpUnits_isOpen R S K L p)

end LocalClassFieldTheory
