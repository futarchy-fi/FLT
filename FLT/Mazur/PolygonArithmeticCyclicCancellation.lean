/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicRestriction

/-!
# Simultaneous cancellation on every edge of a cycle

The positive field on the successor and complementary field on the current
node cancel the measured error. No edge, including the closing edge, is omitted.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (S : State R π ι) (hS : S.Compatible)
  (r : ℕ) (hr : S.Normalized r)
local notation "q" => S.nextIntegralField hS r hr
local notation "e" => S.nextField hS r hr
local notation "Q" => Quotient R π (r + 1)

/-- The incoming field at the actual successor is the negative positive error on this edge. -/
theorem State.nextField_incoming (i : ι) :
    correctionField R π (r + 1) (nodeField σ q (σ i) false) = -positivePart (e i) := by
  change correctionField R π (r + 1) (-positivePart (q (σ.symm (σ i)))) = _
  rw [Equiv.symm_apply_apply]
  change PolygonScalingNaturality.coeffMap (algebraMap R Q) (-positivePart (q i)) = _
  rw [map_neg]
  change -correctionField R π (r + 1) (positivePart (q i)) = _
  rw [correctionField_positive, S.nextIntegralField_spec]

/-- The outgoing field is the reciprocal complementary error on the same edge. -/
theorem State.nextField_outgoing (i : ι) :
    correctionField R π (r + 1) (nodeField σ q i true) =
      reciprocalField (nonpositivePart (e i)) := by
  change correctionField R π (r + 1) (reciprocalField (nonpositivePart (q i))) = _
  rw [correctionField_reciprocal, S.nextIntegralField_spec]

/-- Each full reciprocal edge is recovered by its two actual incident node factors. -/
theorem State.next_edge (ha : S.Annihilated) (i : ι) :
    (S.step σ q r).edge (r + 1) i = invert := by
  change ((S.punctureFactor σ q r (r + 1) (σ i) false).trans
    (S.edge (r + 1) i)).trans (S.punctureFactor σ q r (r + 1) i true).symm = _
  rw [S.punctureFactor_next σ q r ha, S.punctureFactor_next σ q r ha,
    S.nextField_incoming σ hS r hr, S.nextField_outgoing σ hS r hr]
  apply LaurentReciprocalRelativeCorrection.cancel_relative
    (PolygonArithmeticStages.parameter R π (r + 1)) (r + 1)
    (nextCorrectionParameter_square R π r)
  · intro z
    change invert z - invert z ∈ _
    rw [sub_self]
    exact Ideal.zero_mem _
  · change ((Ideal.span {PolygonArithmeticStages.parameter R π (r + 1)}).map
      (algebraMap Q Q[T;T⁻¹])) ^ (1 + (r + 1)) = ⊥
    rw [Nat.add_comm 1, ← Ideal.map_pow, Ideal.span_singleton_pow,
      parameter_pow, Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    exact S.nextField_subst hS r hr i

/-- A measured cyclic correction advances normalization of the entire loop by one order. -/
theorem State.next_normalized (ha : S.Annihilated) :
    (S.step σ q r).Normalized (r + 1) := S.next_edge σ hS r hr ha

end FLT.Mazur.PolygonArithmeticCyclic
