/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualIntegralLift
public import FLT.Mazur.PolygonArithmeticTwoBranchCorrectionLift

/-!
# A compatible terminal correction from both actual residual fields

The two positive integral fields give one common full terminal node at every
arithmetic order. Its quotient squares and first-order smoothing agree with
the original arithmetic system. Identification of the entire first-order
composition with the earlier terminal factor is a separate comparison.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentBoundaryCorrectionSplit
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "σ" => fun m ↦ arithmeticTerminalChangedSmoothing data H m j hj u hu

/-- The two integral positive fields are taken from the actual residual coordinates. -/
def arithmeticTerminalIntegralField (b : Bool) : R[T;T⁻¹] :=
  positivePart (arithmeticResidualIntegralField hπ data H j hj u hu b)

local notation "q" => arithmeticTerminalIntegralField hπ data H j hj u hu
local notation "s" => fun m ↦ twoBranchCorrectionSmoothing R π m (σ m) q

/-- The complete original positive field is recovered on each first-order branch. -/
theorem arithmeticTerminalIntegralField_first (b : Bool) :
    correctionField R π 1 (q b) =
      positivePart (arithmeticFirstResidualField hπ data H j hj u hu b) := by
  rw [arithmeticTerminalIntegralField, correctionField_positive,
    arithmeticResidualIntegralField_first]

/-- One whole terminal node realizes both lifted positive fields at every arithmetic order. -/
irreducible_def arithmeticResidualTerminalLift (m : ℕ) :
    ChartRing (s m) ≃ₐ[Quotient R π m] ChartRing (σ m) :=
  twoBranchCorrectionNodeFactor R π m (σ m) q

/-- The terminal correction has the original terminal smoothing at first order. -/
theorem arithmeticResidualTerminalLift_smoothing_first : s 1 = σ 1 :=
  twoBranchCorrectionSmoothing_first R π (σ 1)
    (arithmeticFirstChangedSmoothing_annihilated data H j hj u hu) q

/-- Both lifted terminal branches share one exact quotient-compatible smoothing. -/
theorem arithmeticResidualTerminalLift_smoothing_restriction (m : ℕ) :
    restriction R π m (s (m + 1)) = s m :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ) q

/-- The whole common terminal factor descends through each original arithmetic quotient. -/
theorem arithmeticResidualTerminalLift_restriction (m : ℕ) :
    (ringMap (restriction R π m).toRingHom (σ (m + 1)) (σ m)
        (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ)).comp
      (arithmeticResidualTerminalLift hπ data H j hj u hu (m + 1)).toAlgHom.toRingHom =
    (arithmeticResidualTerminalLift hπ data H j hj u hu m).toAlgHom.toRingHom.comp
      (ringMap (restriction R π m).toRingHom (s (m + 1)) (s m)
        (arithmeticResidualTerminalLift_smoothing_restriction hπ data H j hj u hu m)) := by
  rw [arithmeticResidualTerminalLift_def, arithmeticResidualTerminalLift_def]
  exact twoBranchCorrectionNodeFactor_restriction R π m _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
