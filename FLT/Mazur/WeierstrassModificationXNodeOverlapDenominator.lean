/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXOppositeNodeGeometry
public import FLT.Mazur.NilpotentPolynomialEvaluation

/-!
# The opposite initial denominator on the full first node

The original opposite denominator differs from -q by an element of the
extended nilpotent coefficient ideal. Its open is therefore exactly D(q).
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "Q" => algebraMap N L (NodalFiber.q s)
local notation "P" => algebraMap N L (NodalFiber.p s)
local notation "E" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "D" => polynomialOppositeDenominator W s b3 b4 b6 r
local notation "J" => I.map (algebraMap R L)
local notation "T" => polynomialNodeInverseT b3 r I hI hrI h3 W P Q
  (polynomialNodeOpen_unit W s)

/-- The full opposite denominator retains its exact polynomial correction on the first node. -/
theorem polynomialNodeForwardBase_oppositeDenominator :
    E D = -Q - (r.eval₂ (algebraMap R L) T + r.eval₂ (algebraMap R L) T +
      algebraMap R L b3 * T) := by
  rw [polynomialOppositeDenominator, map_add, map_neg, AlgHom.commutes]
  change -polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 P Q _ _ _ + _ = _
  rw [polynomialNodeEvaluation_opposite]
  ring

/-- The error from -q lies in the actual extended arithmetic ideal. -/
theorem polynomialNodeForwardBase_oppositeDenominator_mem : E D + Q ∈ J := by
  rw [polynomialNodeForwardBase_oppositeDenominator]
  have he := NilpotentPolynomialInverse.eval₂_mem I (algebraMap R L) r hrI T
  have hm : algebraMap R L b3 * T ∈ J :=
    (J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  convert (J).neg_mem ((J).add_mem ((J).add_mem he he) hm) using 1; ring

/-- Every prime of the full node contains the opposite denominator exactly when it contains q. -/
theorem polynomialNodeForwardBase_oppositeDenominator_mem_iff (z : PrimeSpectrum L) :
    E D ∈ z.asIdeal ↔ Q ∈ z.asIdeal := by
  have hn : IsNilpotent (E D + Q) := NilpotentQuadraticRoot.element_nilpotent J
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI (algebraMap R L))
    (polynomialNodeForwardBase_oppositeDenominator_mem W s b3 b4 b6 r hr I hI hrI h3)
  have hz := (nilpotent_iff_mem_prime.mp hn) z.asIdeal z.isPrime
  constructor
  · intro h
    simpa only [add_sub_cancel_left] using z.asIdeal.sub_mem hz h
  · intro h
    simpa only [add_sub_cancel_right] using z.asIdeal.sub_mem hz h

/-- The inverse image of the entire opposite node is precisely the first node's full D(q). -/
theorem polynomialNodeChart_opposite_preimage :
    (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3) ⁻¹'
      Set.range (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3) =
        (PrimeSpectrum.basicOpen Q : Set (PrimeSpectrum L)) := by
  rw [polynomialOppositeNodeChart_range, polynomialNodeChart_eq_spec]
  ext z
  change (E D ∉ z.asIdeal) ↔ Q ∉ z.asIdeal
  exact not_congr
    (polynomialNodeForwardBase_oppositeDenominator_mem_iff W s b3 b4 b6 r hr I hI hrI h3 z)

end FLT.Mazur.WeierstrassModificationX
