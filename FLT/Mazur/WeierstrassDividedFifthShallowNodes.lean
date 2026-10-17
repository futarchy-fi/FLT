/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowFields
public import FLT.Mazur.WeierstrassDividedFourthSmoothingAnnihilation

/-!
# Full fifth node factors for the original initial edge

Both endpoints start on their complete fourth smoothings. The earlier neighbor's
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
local notation "s" => arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticFourthShallowSmoothing hπ data H j hj u hu m
local notation "A" => arithmeticFifthShallowIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthShallowNeighborIntegralField hπ data H j hj u hu

/-- The corrected initial node keeps its full new smoothing. -/
def arithmeticFifthShallowSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m (e b) (A b)

/-- The full initial factor uses the corrected fourth initial smoothing. -/
def arithmeticFifthShallowFactor (b : Bool) :
    ChartRing (arithmeticFifthShallowSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (e b) := correctionNodeFactor R π m (e b) (A b)

/-- The earlier neighbor's two fields retain both resulting scalar drifts. -/
def arithmeticFifthShallowNeighborSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (P b)

/-- The depth-two earlier neighbor factor includes both incident fifth corrections. -/
def arithmeticFifthShallowNeighborFactor (b : Bool) :
    ChartRing (arithmeticFifthShallowNeighborSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (P b)

/-- Both initial punctures come from its one whole-node factor. -/
theorem arithmeticFifthShallowFactor_puncture (b a : Bool) :
    (punctureLaurentMap (e b) a).comp
        (arithmeticFifthShallowFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m (e b) (A b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFifthShallowSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m (e b) (A b) a

/-- Both neighboring punctures likewise come from the same full corrected earlier neighbor. -/
theorem arithmeticFifthShallowNeighborFactor_puncture (b a : Bool) :
    (punctureLaurentMap (s b) a).comp
        (arithmeticFifthShallowNeighborFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFifthShallowNeighborSmoothing
          hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (P b) a

omit m in
/-- The full initial outgoing substitution realizes its complete relative field at layer five. -/
theorem arithmeticFifthShallowPuncture_fifth (b : Bool) :
    correctionPunctureFactor R π 5
        (arithmeticFourthShallowSmoothing hπ data H j hj u hu 5 b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4)
        (reciprocalField (nonpositivePart
          (arithmeticFifthResidualField hπ data H j hj u hu .shallow b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 5 _ (A b) true (LaurentPolynomial.T 1) = _
  rw [arithmeticFifthShallowIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticFifthShallowField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticFifthShallowField_boundary hπ data H j hj u hu b

omit m in
/-- Both chosen fields on the full fourth neighbor smoothing are realized at layer five. -/
theorem arithmeticFifthShallowNeighborPuncture_fifth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5
        (arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu 5 b) (P b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4) (correctionField R π 5
          (arithmeticFifthShallowNeighborField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 5 4
    (nextCorrectionParameter_square R π 4) _
    (by
      apply twoBranchCorrectionSmoothing_annihilated
      exact arithmeticFourthEarlierInput_annihilated hπ data H j hj u hu 5 b) _
    (arithmeticFifthShallowNeighborField_boundary hπ data H j hj u hu b) a

end FLT.Mazur.WeierstrassDividedDepth
