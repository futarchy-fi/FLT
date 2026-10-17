/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdJointIdentification
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Third-layer identification of the earlier and terminal full node factors

The positive predecessor field acts on the earlier retained node. Both closing
fields act on the same terminal with its actual twice corrected smoothing.
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
local notation "Q" => Quotient R π 3
local notation "e" => parameter R π 3 ^ 3
local notation "he" => nextCorrectionParameter_square R π 2
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3
local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu 3
local notation "q" => arithmeticThirdResidualField hπ data H j hj u hu
local notation "v" => arithmeticThirdResidualIntegralField hπ data H j hj u hu

/-- The full positive predecessor field acts on the entire earlier retained node. -/
def arithmeticThirdEarlierLayerFactor (b : Bool) : ChartRing τ ≃ₐ[Q] ChartRing τ :=
  squareZeroPositiveFactor τ e he (arithmeticTopSmoothing_annihilated data H 3) (q .preceding b)

/-- Both positive closing fields act on one full terminal at its actual previous smoothing. -/
def arithmeticThirdTerminalLayerFactor : ChartRing t ≃ₐ[Q] ChartRing t :=
  squareZeroTwoBranchFactor t e he
    (arithmeticThirdTerminalInput_annihilated hπ data H j hj u hu) (q .closing)

/-- The full earlier lift specializes to its entire positive square-zero factor. -/
theorem arithmeticThirdEarlierFactor_third (b : Bool) :
    (arithmeticThirdEarlierFactor hπ data H j hj u hu 3 b).toAlgHom.toRingHom =
      (arithmeticThirdEarlierLayerFactor hπ data H j hj u hu b).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id Q)
          (arithmeticThirdEarlierSmoothing hπ data H j hj u hu 3 b) τ
          (arithmeticThirdEarlierSmoothing_third hπ data H j hj u hu b)) := by
  have h := correctionNodeFactor_higher_eq R π 3 2 τ
    (arithmeticTopSmoothing_annihilated data H 3) (positivePart (v .preceding b))
  rw [correctionField_positive, arithmeticThirdResidualIntegralField_spec] at h
  exact h

/-- The full rebased terminal lift recovers both square-zero corrections on its actual old node. -/
theorem arithmeticThirdTerminalFactor_third :
    (ringMap (RingHom.id Q)
        (arithmeticThirdTerminalSmoothing hπ data H j hj u hu 3) t
        (arithmeticThirdTerminalSmoothing_third hπ data H j hj u hu)).comp
      (arithmeticThirdTerminalFactor hπ data H j hj u hu 3).toAlgHom.toRingHom =
        (arithmeticThirdTerminalLayerFactor hπ data H j hj u hu).toAlgHom.toRingHom := by
  apply twoBranchCorrectionRebasedFactor_higher_eq R π 3 2 he t
    (arithmeticThirdTerminalInput_annihilated hπ data H j hj u hu)
    (fun b ↦ positivePart (v .closing b)) (q .closing)
  intro b
  rw [correctionField_positive, arithmeticThirdResidualIntegralField_spec]

end FLT.Mazur.WeierstrassDividedDepth
