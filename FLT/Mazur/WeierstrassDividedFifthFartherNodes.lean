/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherFields
public import FLT.Mazur.WeierstrassDividedFifthDeepNodes

/-!
# Full fifth node factors for the original initial edge

The initial endpoint starts on its original smoothing; its neighbor uses its fourth smoothing.
The earlier neighbor's
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
local notation "s" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "e" => fun (_ : Bool) ↦
  arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthFartherIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthFartherNeighborIntegralField hπ data H j hj u hu

/-- The original initial node keeps its full new smoothing. -/
def arithmeticFifthFartherSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m (e b) (A b)

/-- The full initial factor uses the original initial smoothing. -/
def arithmeticFifthFartherFactor (b : Bool) :
    ChartRing (arithmeticFifthFartherSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (e b) := correctionNodeFactor R π m (e b) (A b)

/-- The earlier neighbor's two fields retain both resulting scalar drifts. -/
def arithmeticFifthFartherNeighborSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (P b)

/-- The depth-three earlier neighbor factor includes both incident fifth corrections. -/
def arithmeticFifthFartherNeighborFactor (b : Bool) :
    ChartRing (arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (P b)

/-- Both initial punctures come from its one whole-node factor. -/
theorem arithmeticFifthFartherFactor_puncture (b a : Bool) :
    (punctureLaurentMap (e b) a).comp
        (arithmeticFifthFartherFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m (e b) (A b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFifthFartherSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m (e b) (A b) a

/-- Both neighboring punctures likewise come from the same full corrected earlier neighbor. -/
theorem arithmeticFifthFartherNeighborFactor_puncture (b a : Bool) :
    (punctureLaurentMap (s b) a).comp
        (arithmeticFifthFartherNeighborFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFifthFartherNeighborSmoothing
          hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (P b) a

omit m in
/-- The full initial outgoing substitution realizes its complete relative field at layer five. -/
theorem arithmeticFifthFartherPuncture_fifth (b : Bool) :
    correctionPunctureFactor R π 5
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 5) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4)
        (reciprocalField (nonpositivePart
          (arithmeticFifthResidualField hπ data H j hj u hu .fartherDirect b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 5 _ (A b) true (LaurentPolynomial.T 1) = _
  rw [arithmeticFifthFartherIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticFifthFartherField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticFifthFartherField_boundary hπ data H j hj u hu b

omit m in
/-- Both neighboring fields are realized on the full fourth smoothing at layer five. -/
theorem arithmeticFifthFartherNeighborPuncture_fifth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5
        (arithmeticFourthFartherSmoothing hπ data H j hj u hu 5 b) (P b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4) (correctionField R π 5
          (arithmeticFifthFartherNeighborField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 5 4
    (nextCorrectionParameter_square R π 4) _
    (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu .farther 5 b) _
    (arithmeticFifthFartherNeighborField_boundary hπ data H j hj u hu b) a

end FLT.Mazur.WeierstrassDividedDepth
