/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialFields
public import FLT.Mazur.WeierstrassDividedFourthPunctureIdentification

/-!
# Full fourth node factors for the original initial edge

Both endpoints start on their exact third smoothings. The predecessor's
incoming field is chosen from the full relative initial residual, while its
outgoing field remains the one needed by the shared interior incoming edge.
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
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "A" => arithmeticFourthInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthInitialNeighborIntegralField hπ data H j hj u hu

/-- The original initial node keeps its full new smoothing. -/
def arithmeticFourthInitialSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m (e b) (A b)

/-- The full initial factor uses the exact smoothing of the already corrected initial open. -/
def arithmeticFourthInitialFactor (b : Bool) :
    ChartRing (arithmeticFourthInitialSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (e b) := correctionNodeFactor R π m (e b) (A b)

/-- The predecessor's two fields retain both resulting scalar drifts. -/
def arithmeticFourthInitialNeighborSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (P b)

/-- The depth-one predecessor factor includes both incident fourth corrections. -/
def arithmeticFourthInitialNeighborFactor (b : Bool) :
    ChartRing (arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (P b)

/-- Both initial punctures come from its one whole-node factor. -/
theorem arithmeticFourthInitialFactor_puncture (b a : Bool) :
    (punctureLaurentMap (e b) a).comp
        (arithmeticFourthInitialFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m (e b) (A b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFourthInitialSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m (e b) (A b) a

/-- Both neighboring punctures likewise come from the same full corrected predecessor. -/
theorem arithmeticFourthInitialNeighborFactor_puncture (b a : Bool) :
    (punctureLaurentMap (s b) a).comp
        (arithmeticFourthInitialNeighborFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFourthInitialNeighborSmoothing
          hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (P b) a

omit m in
/-- The full initial outgoing substitution realizes its complete relative field at layer four. -/
theorem arithmeticFourthInitialPuncture_fourth (b : Bool) :
    correctionPunctureFactor R π 4
        (arithmeticThirdEarlierSmoothing hπ data H j hj u hu 4 b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 4 ^ 4)
        (nextCorrectionParameter_square R π 3)
        (reciprocalField (nonpositivePart
          (arithmeticFourthResidualField hπ data H j hj u hu .initial b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 4 _ (A b) true (LaurentPolynomial.T 1) = _
  rw [arithmeticFourthInitialIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticFourthInitialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticFourthInitialField_boundary hπ data H j hj u hu b

omit m in
/-- The predecessor realizes both chosen fields on its actual third smoothing at layer four. -/
theorem arithmeticFourthInitialNeighborPuncture_fourth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 4
        (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 4 b) (P b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 4 ^ 4)
        (nextCorrectionParameter_square R π 3) (correctionField R π 4
          (arithmeticFourthInitialNeighborField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 4 3
    (nextCorrectionParameter_square R π 3) _
    (arithmeticFourthPrecedingInput_annihilated hπ data H j hj u hu 4 b) _
    (arithmeticFourthInitialNeighborField_boundary hπ data H j hj u hu b) a

end FLT.Mazur.WeierstrassDividedDepth
