/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthPunctureIdentification
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# The installed fourth finite fields are the actual residual projections

These identifications retain every Laurent coefficient and the incoming
minus signs. They relate the full node substitutions to the interior edge errors.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 4
local notation "p" => fun b a ↦ correctionField R π 4
  (arithmeticFourthLastField hπ data H j hj u hu b a)
local notation "r" => fun b a ↦ correctionField R π 4
  (arithmeticFourthPrecedingField hπ data H j hj u hu b a)
local notation "q" => arithmeticFourthResidualField hπ data H j hj u hu

/-- The last outgoing field is the reciprocal of the complete nonpositive closing field. -/
theorem arithmeticFourthLastLayerField_outgoing (b : Bool) :
    p b true = reciprocalField (nonpositivePart (q .closing b)) := by
  change correctionField R π 4 (reciprocalField (nonpositivePart _)) = _
  rw [correctionField_reciprocal, arithmeticFourthResidualIntegralField_spec]

/-- The last incoming field has the required negative complementary incoming sign. -/
theorem arithmeticFourthLastLayerField_incoming (b : Bool) :
    p b false = -reciprocalField (nonpositivePart (q .incoming b)) := by
  change correctionField R π 4 (-reciprocalField (nonpositivePart _)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 4 (-z) = -correctionField R π 4 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R Q)) z,
    correctionField_reciprocal, arithmeticFourthResidualIntegralField_spec]

/-- The predecessor supplies the complete remaining positive shared incoming field. -/
theorem arithmeticFourthPrecedingLayerField_outgoing (b : Bool) :
    r b true = positivePart (q .incoming b) := by
  change correctionField R π 4 (positivePart _) = _
  rw [correctionField_positive, arithmeticFourthResidualIntegralField_spec]

/-- Its opposite field is the negative complementary predecessor incoming field. -/
theorem arithmeticFourthPrecedingLayerField_incoming (b : Bool) :
    r b false = -reciprocalField (nonpositivePart (q .preceding b)) := by
  change correctionField R π 4 (-reciprocalField (nonpositivePart _)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 4 (-z) = -correctionField R π 4 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R Q)) z,
    correctionField_reciprocal, arithmeticFourthResidualIntegralField_spec]

end FLT.Mazur.WeierstrassDividedDepth
