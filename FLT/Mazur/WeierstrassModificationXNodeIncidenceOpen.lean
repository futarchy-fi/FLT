/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapDenominator
public import FLT.Mazur.WeierstrassModificationXStandardPuncture

/-!
# The original incidence open on both full initial nodes

The full original D(t) pulls back to D(p) on either initial label. This
puncture differs from the D(q) overlap of the two initial neighborhoods.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "P" => algebraMap N L (NodalFiber.p s)
local notation "Q" => algebraMap N L (NodalFiber.q s)
local notation "E" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "T" => polynomialNodeInverseT b3 r I hI hrI h3 W P Q
  (polynomialNodeOpen_unit W s)
local notation "J" => I.map (algebraMap R L)

/-- The corrected opposite factor stays invertible on the entire initial node neighborhood. -/
theorem polynomialNodeForwardBase_opposite_isUnit :
    IsUnit (E (polynomialOppositeFactor W s b3 b4 b6 r)) := by
  change IsUnit (polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 P Q _ _ _)
  rw [polynomialNodeEvaluation_opposite]
  have he := NilpotentPolynomialInverse.eval₂_mem I (algebraMap R L) r hrI T
  have hm : algebraMap R L b3 * T ∈ J :=
    (J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  have hn := NilpotentQuadraticRoot.element_nilpotent J
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI (algebraMap R L))
    ((J).add_mem ((J).add_mem he he) hm)
  exact hn.isUnit_add_left_of_commute (polynomialNodeOpen_unit W s) (mul_comm _ _)

/-- The full incidence and the first node coordinate vanish at exactly the same primes. -/
theorem polynomialNodeForwardBase_t_mem_iff (z : PrimeSpectrum L) :
    E (t W s b3 b4 b6) ∈ z.asIdeal ↔ P ∈ z.asIdeal := by
  have hp : E (t W s b3 b4 b6) * E (polynomialOppositeFactor W s b3 b4 b6 r) = P := by
    rw [← map_mul]
    exact polynomialNodeEvaluation_first ..
  rw [← hp]
  exact (z.asIdeal.mul_unit_mem_iff_mem
    (polynomialNodeForwardBase_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3)).symm

/-- The original incidence open on the first full node is exactly D(p). -/
theorem polynomialNodeChart_incidence_preimage :
    (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3) ⁻¹'
      (PrimeSpectrum.basicOpen (t W s b3 b4 b6) : Set (PrimeSpectrum A)) =
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum L)) := by
  rw [polynomialNodeChart_eq_spec]
  ext z
  exact not_congr (polynomialNodeForwardBase_t_mem_iff W s b3 b4 b6 r hr I hI hrI h3 z)

/-- Reflection preserves the original incidence open on the opposite full node. -/
theorem polynomialOppositeNodeChart_incidence_preimage :
    (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3) ⁻¹'
      (PrimeSpectrum.basicOpen (t W s b3 b4 b6) : Set (PrimeSpectrum A)) =
        (PrimeSpectrum.basicOpen P : Set (PrimeSpectrum L)) := by
  rw [polynomialOppositeNodeChart_eq_spec]
  ext z
  change E ((initialReflection W s b3 b4 b6) (t W s b3 b4 b6)) ∉ z.asIdeal ↔ _
  rw [initialReflection_t]
  exact not_congr (polynomialNodeForwardBase_t_mem_iff W s b3 b4 b6 r hr I hI hrI h3 z)

end FLT.Mazur.WeierstrassModificationX
