/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterFields
public import FLT.Mazur.WeierstrassDividedFourthPunctureIdentification

/-!
# Full fourth factors on both sides of the further retained incoming edge

The earlier factor uses its actual third smoothing and both incident fields.
The farther factor uses the unmodified normalized smoothing. Both retain full scalar drifts.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "P" => arithmeticFourthOuterIntegralField hπ data H j hj u hu
local notation "A" => arithmeticFourthFartherIntegralField hπ data H j hj u hu

/-- The earlier node retains the simultaneous drift from both fourth fields. -/
def arithmeticFourthOuterSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (P b)

/-- The entire earlier node receives both incident corrections from its third source. -/
def arithmeticFourthOuterFactor (b : Bool) :
    ChartRing (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (P b)

/-- The farther retained node keeps its new full smoothing. -/
def arithmeticFourthFartherSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m τ (A b)

/-- The farther node factor extends its positive field across the entire node. -/
def arithmeticFourthFartherFactor (b : Bool) :
    ChartRing (arithmeticFourthFartherSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing τ := correctionNodeFactor R π m τ (A b)

/-- Both earlier punctures come from the same whole-node factor. -/
theorem arithmeticFourthOuterFactor_puncture (b a : Bool) :
    (punctureLaurentMap (s b) a).comp
        (arithmeticFourthOuterFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (P b) a

/-- Both farther punctures likewise come from one full node factor. -/
theorem arithmeticFourthFartherFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticFourthFartherFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m τ (A b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFourthFartherSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m τ (A b) a

omit m in
/-- Both earlier punctures realize their complete fields on the actual third smoothing. -/
theorem arithmeticFourthOuterPuncture_fourth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 4
        (arithmeticThirdEarlierSmoothing hπ data H j hj u hu 4 b) (P b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 4 ^ 4)
        (nextCorrectionParameter_square R π 3)
        (correctionField R π 4 (arithmeticFourthOuterField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 4 3
    (nextCorrectionParameter_square R π 3) _
    (arithmeticFourthEarlierInput_annihilated hπ data H j hj u hu 4 b) _
    (arithmeticFourthOuterField_boundary hπ data H j hj u hu b) a

omit m in
/-- The farther puncture realizes its full positive field at layer four. -/
theorem arithmeticFourthFartherPuncture_fourth (b : Bool) :
    correctionPunctureFactor R π 4
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 4) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 4 ^ 4)
        (nextCorrectionParameter_square R π 3)
        (positivePart (arithmeticFourthResidualField hπ data H j hj u hu .earlierIncoming b)) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 4 _ (A b) true (LaurentPolynomial.T 1) = _
  rw [arithmeticFourthFartherIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticFourthFartherField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticFourthFartherField_boundary hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
