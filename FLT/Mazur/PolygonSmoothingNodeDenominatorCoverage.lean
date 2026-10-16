/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingNodeBasicOpen

/-!
# The marking denominator on the entire coordinate-node locus

The same denominator is one modulo every ideal containing both original
coordinates. Thus its principal open contains every node prime over any
base, without changing the ring or discarding its nilpotents.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
variable {R A : Type*} [CommRing R] [CommRing A] (t : R)
variable (f : ChartRing t →+* A)

/-- Every specialization killing both coordinates sends the actual denominator to one. -/
theorem nodeMarkingDenominator_map_eq_one
    (hx : f (leftCoordinate t) = 0) (hy : f (rightCoordinate t) = 0) :
    f (nodeMarkingDenominator t) = 1 := by
  rw [nodeMarkingDenominator, f.map_mul, f.map_sub, f.map_sub, f.map_one,
    hx, hy, sub_zero, mul_one]

/-- The original denominator is one in the full quotient by any coordinate-node ideal. -/
theorem nodeMarkingDenominator_quotient_eq_one (I : Ideal A)
    (hx : f (leftCoordinate t) ∈ I) (hy : f (rightCoordinate t) ∈ I) :
    Ideal.Quotient.mk I (f (nodeMarkingDenominator t)) = 1 :=
  nodeMarkingDenominator_map_eq_one t ((Ideal.Quotient.mk I).comp f)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hx) (Ideal.Quotient.eq_zero_iff_mem.mpr hy)

/-- No proper ideal containing the two original coordinates contains the denominator. -/
theorem nodeMarkingDenominator_not_mem (I : Ideal A) (hI : I ≠ ⊤)
    (hx : f (leftCoordinate t) ∈ I) (hy : f (rightCoordinate t) ∈ I) :
    f (nodeMarkingDenominator t) ∉ I := by
  intro hd
  have he := nodeMarkingDenominator_quotient_eq_one t f I hx hy
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hd] at he
  apply hI
  apply Ideal.eq_top_of_isUnit_mem I _ isUnit_one
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (map_one (Ideal.Quotient.mk I)).trans he.symm

/-- All coordinate-node primes lie in the unchanged marking-denominator open. -/
theorem nodeMarkingDenominator_node_coverage (p : PrimeSpectrum A)
    (hx : f (leftCoordinate t) ∈ p.asIdeal) (hy : f (rightCoordinate t) ∈ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen (f (nodeMarkingDenominator t)) :=
  nodeMarkingDenominator_not_mem t f p.asIdeal p.isPrime.ne_top hx hy

end FLT.Mazur.PolygonSmoothing
