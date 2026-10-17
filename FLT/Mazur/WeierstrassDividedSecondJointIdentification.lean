/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointFields
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Simultaneous second-layer identification on the shared retained node

Both incoming and closing fields live on the same complete node factor.
Its two full puncture substitutions are independently identified at stage two.
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
local notation "Q" => Quotient R π 2
local notation "e" => parameter R π 2 ^ 2
local notation "he" => nextCorrectionParameter_square R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 2
local notation "v" => arithmeticSecondJointRetainedField hπ data H j hj u hu
local notation "V" => arithmeticSecondJointRetainedIntegralField hπ data H j hj u hu
local notation "q" => arithmeticSecondResidualField hπ data H j hj u hu

/-- The actual pair of full finite fields on each shared retained node. -/
def arithmeticSecondJointRetainedLayerField (b a : Bool) : Q[T;T⁻¹] :=
  correctionField R π 2 (v b a)

local notation "p" => arithmeticSecondJointRetainedLayerField hπ data H j hj u hu

/-- The outgoing field is precisely the complementary closing field in reciprocal coordinate. -/
theorem arithmeticSecondJointRetainedLayerField_outgoing (b : Bool) :
    p b true = reciprocalField (nonpositivePart (q false b)) := by
  change correctionField R π 2 (reciprocalField (nonpositivePart _)) = _
  rw [correctionField_reciprocal, arithmeticSecondResidualIntegralField_spec]

/-- The opposite field carries the negative complementary incoming error. -/
theorem arithmeticSecondJointRetainedLayerField_incoming (b : Bool) :
    p b false = -reciprocalField (nonpositivePart (q true b)) := by
  change correctionField R π 2 (-reciprocalField (nonpositivePart _)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 2 (-z) = -correctionField R π 2 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R Q)) z,
    correctionField_reciprocal, arithmeticSecondResidualIntegralField_spec]

/-- Each full finite field is already strictly positive in its own node coordinate. -/
theorem arithmeticSecondJointRetainedLayerField_positive (b a : Bool) :
    positivePart (p b a) = p b a := by
  ext d
  rw [positivePart_coeff]
  split_ifs with hd
  · rfl
  · exact (correctionField_boundary R π 2 (v b a)
      (arithmeticSecondJointRetainedField_boundary hπ data H j hj u hu b a) d
      (by omega)).symm

/-- One entire square-zero node factor realizes the two prescribed finite fields. -/
def arithmeticSecondJointRetainedLayerFactor (b : Bool) : ChartRing τ ≃ₐ[Q] ChartRing τ :=
  squareZeroTwoBranchFactor τ e he (arithmeticSecondSmoothing_annihilated data H) (p b)

/-- The actual higher shared-node lift recovers that one full node automorphism. -/
theorem arithmeticSecondJointRetainedFactor_second (b : Bool) :
    (arithmeticSecondJointRetainedFactor hπ data H j hj u hu 2 b).toAlgHom.toRingHom =
      (arithmeticSecondJointRetainedLayerFactor hπ data H j hj u hu b).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id Q) (twoBranchCorrectionSmoothing R π 2 τ (V b)) τ
          (arithmeticSecondJointRetainedSmoothing_pair hπ data H j hj u hu 2 b)) := by
  apply twoBranchCorrectionNodeFactor_higher_eq R π 2 1 he τ
    (arithmeticSecondSmoothing_annihilated data H) (v b) (p b)
  intro a
  exact (arithmeticSecondJointRetainedLayerField_positive hπ data H j hj u hu b a).symm

/-- Both full substitutions are identified simultaneously from the same shared-node lift. -/
theorem arithmeticSecondJointRetainedPuncture_second (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 2 τ (V b) a =
      LaurentSquareZeroAutomorphism.equiv e he (p b a) := by
  apply punctureFactor_source_identification _ τ
    (arithmeticSecondJointRetainedSmoothing_pair hπ data H j hj u hu 2 b)
    (arithmeticSecondJointRetainedFactor hπ data H j hj u hu 2 b)
    (arithmeticSecondJointRetainedLayerFactor hπ data H j hj u hu b) _ _ a
    (arithmeticSecondJointRetainedFactor_second hπ data H j hj u hu b)
    (arithmeticSecondJointRetainedFactor_puncture hπ data H j hj u hu 2 b a)
  have hh := squareZeroTwoBranchFactor_boundary τ e he
    (arithmeticSecondSmoothing_annihilated data H) (p b) a
  rw [arithmeticSecondJointRetainedLayerField_positive] at hh
  cases a <;> exact hh

end FLT.Mazur.WeierstrassDividedDepth
