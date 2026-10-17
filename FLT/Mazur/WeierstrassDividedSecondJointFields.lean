/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondResidualIdentification

/-!
# Simultaneous integral fields for the incoming and closing second errors

Each shared retained node receives a closing correction on its outgoing
puncture and the negative incoming correction on its opposite puncture.
The remaining positive incoming part is assigned to the preceding node.
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
local notation "q" => arithmeticSecondResidualIntegralField hπ data H j hj u hu

/-- Two independent corrections on the two punctures of each shared retained node. -/
def arithmeticSecondJointRetainedField (b a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q false b))
  else -reciprocalField (nonpositivePart (q true b))

local notation "v" => arithmeticSecondJointRetainedField hπ data H j hj u hu

/-- Both shared-node fields have zero linear coefficient before any quotient is chosen. -/
theorem arithmeticSecondJointRetainedField_linear (b a : Bool) : (v b a).coeff 1 = 0 := by
  cases a <;> simp only [arithmeticSecondJointRetainedField, Bool.false_eq_true, ↓reduceIte,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, reciprocalField_coeff,
    nonpositivePart_coeff] <;> norm_num

/-- Both complete shared-node fields vanish at their original boundary origins. -/
theorem arithmeticSecondJointRetainedField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (v b a).coeff d = 0 := by
  cases a
  · change (-reciprocalField (nonpositivePart (q true b))).coeff d = 0
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      reciprocal_nonpositive_coeff _ d hd, neg_zero]
  · exact reciprocal_nonpositive_coeff _ d hd

/-- The predecessor receives the entire positive part of the incoming residual field. -/
def arithmeticSecondPrecedingIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1 (positivePart (q true b))

/-- The shared retained fields are scaled once to the second arithmetic order. -/
def arithmeticSecondJointRetainedIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1 (v b a)

variable (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "V" => arithmeticSecondJointRetainedIntegralField hπ data H j hj u hu

/-- Each of the two shared retained corrections preserves the smoothing at every order. -/
theorem arithmeticSecondJointRetainedSmoothing (b a : Bool) :
    correctionSmoothing R π m τ (V b a) = τ := by
  rw [correctionSmoothing, arithmeticSecondJointRetainedIntegralField,
    higherCorrectionField_coeff, arithmeticSecondJointRetainedField_linear,
    mul_zero, map_zero, mul_zero, add_zero, one_mul]

/-- The one common smoothing remains unchanged after composing both retained corrections. -/
theorem arithmeticSecondJointRetainedSmoothing_pair (b : Bool) :
    twoBranchCorrectionSmoothing R π m τ (V b) = τ := by
  unfold twoBranchCorrectionSmoothing
  rw [arithmeticSecondJointRetainedSmoothing, arithmeticSecondJointRetainedSmoothing]

/-- One whole-node lift contains both the incoming and closing corrections. -/
def arithmeticSecondJointRetainedFactor (b : Bool) :
    ChartRing (twoBranchCorrectionSmoothing R π m τ (V b)) ≃ₐ[Q] ChartRing τ :=
  twoBranchCorrectionNodeFactor R π m τ (V b)

/-- The preceding whole-node factor includes its exact linear smoothing drift. -/
def arithmeticSecondPrecedingFactor (b : Bool) :
    ChartRing (correctionSmoothing R π m τ
      (arithmeticSecondPrecedingIntegralField hπ data H j hj u hu b)) ≃ₐ[Q] ChartRing τ :=
  correctionNodeFactor R π m τ (arithmeticSecondPrecedingIntegralField hπ data H j hj u hu b)

/-- Both shared retained punctures are realized by that same complete node factor. -/
theorem arithmeticSecondJointRetainedFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticSecondJointRetainedFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m τ (V b) a).toAlgHom.comp
        (punctureLaurentMap (twoBranchCorrectionSmoothing R π m τ (V b)) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m τ (V b) a

end FLT.Mazur.WeierstrassDividedDepth
