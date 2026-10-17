/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialFields
public import FLT.Mazur.WeierstrassDividedFourthJointRestriction
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# The fifth whole last-node factor for the depth-one chain

Its incoming field is selected from the initial-neighbor residual; its
outgoing field retains the common closing correction. Both live on one node.
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
  (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "V" => arithmeticFifthInitialLastIntegralField hπ data H j hj u hu
/-- Either last-node correction preserves any input smoothing at every arithmetic order. -/
theorem arithmeticFifthInitialLastSmoothing (x : Q) (b a : Bool) :
    correctionSmoothing R π m x (V b a) = x := by
  rw [correctionSmoothing, arithmeticFifthInitialLastIntegralField, higherCorrectionField_coeff,
    arithmeticFifthInitialLastField_linear, mul_zero, map_zero, mul_zero, add_zero, one_mul]

/-- The shared full fifth correction preserves the last node's exact smoothing. -/
theorem arithmeticFifthInitialLastSmoothing_pair (b : Bool) :
    twoBranchCorrectionSmoothing R π m τ (V b) = τ := by
  unfold twoBranchCorrectionSmoothing
  rw [arithmeticFifthInitialLastSmoothing, arithmeticFifthInitialLastSmoothing]

/-- Both fields live on one entire last retained node factor. -/
def arithmeticFifthInitialLastFactor (b : Bool) :
    ChartRing (twoBranchCorrectionSmoothing R π m τ (V b)) ≃ₐ[Q] ChartRing τ :=
  twoBranchCorrectionNodeFactor R π m τ (V b)

/-- Both full last-node punctures come from the same whole-node correction. -/
theorem arithmeticFifthInitialLastFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticFifthInitialLastFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m τ (V b) a).toAlgHom.comp
        (punctureLaurentMap (twoBranchCorrectionSmoothing R π m τ (V b)) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m τ (V b) a

omit m in
/-- Both fifth-layer punctures realize their complete depth-one fields. -/
theorem arithmeticFifthInitialLastPuncture_fifth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 5) (V b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4) (correctionField R π 5
          (arithmeticFifthInitialLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 5 4
    (nextCorrectionParameter_square R π 4) _ (arithmeticTopSmoothing_annihilated data H 5) _
    (arithmeticFifthInitialLastField_boundary hπ data H j hj u hu b) a

/-- The entire depth-one last factor retains its full original coefficient square. -/
theorem arithmeticFifthInitialLastFactor_restriction (b : Bool) :
    (ringMap (restriction R π m).toRingHom
      (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π (m + 1)) τ
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
        (arithmeticFifthInitialLastFactor hπ data H j hj u hu (m + 1) b).toAlgHom.toRingHom =
      (arithmeticFifthInitialLastFactor hπ data H j hj u hu m b).toAlgHom.toRingHom.comp
        (ringMap (restriction R π m).toRingHom _ _
          (twoBranchCorrectionSmoothing_restriction R π m _ _
            (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) (V b))) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) (V b)

end FLT.Mazur.WeierstrassDividedDepth
