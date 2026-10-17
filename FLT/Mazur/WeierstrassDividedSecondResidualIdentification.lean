/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondResidualLifts
public import FLT.Mazur.PolygonArithmeticHigherRebaseIdentification

/-!
# Identification of the actual second residual node lifts

At stage two the lifted terminal and retained factors are exactly the
constructed square-zero factors, with both parameter identifications explicit.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 2
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H 2 j hj u hu
local notation "s'" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu 2
local notation "q" => arithmeticSecondResidualIntegralField hπ data H j hj u hu false
local notation "N" => arithmeticSecondRetainedIntegralField hπ data H j hj u hu
local notation "p" => arithmeticSecondResidualField hπ data H j hj u hu false

/-- The full second terminal smoothing is unchanged on its defining square-zero layer. -/
theorem arithmeticSecondResidualLiftSmoothing_second : s' = s :=
  twoBranchCorrectionRebasedSmoothing_higher_eq R π 2 1 s
    (arithmeticSecondResidualSmoothing_annihilated hπ data H j hj u hu)
    (fun b ↦ positivePart (q b))

/-- The entire rebased second terminal factor recovers the actual square-zero node factor. -/
theorem arithmeticSecondResidualLiftTerminalFactor_second :
    (ringMap (RingHom.id Q) s' s
        (arithmeticSecondResidualLiftSmoothing_second hπ data H j hj u hu)).comp
      (arithmeticSecondResidualLiftTerminalFactor hπ data H j hj u hu 2).toAlgHom.toRingHom =
        (arithmeticSecondResidualTerminalFactor hπ data H j hj u hu).toAlgHom.toRingHom := by
  apply twoBranchCorrectionRebasedFactor_higher_eq R π 2 1
    (nextCorrectionParameter_square R π 1) s
    (arithmeticSecondResidualSmoothing_annihilated hπ data H j hj u hu)
    (fun b ↦ positivePart (q b)) p
  intro b
  rw [correctionField_positive, arithmeticSecondResidualIntegralField_spec]

/-- The full retained second lift recovers the complementary square-zero factor. -/
theorem arithmeticSecondResidualLiftRetainedFactor_second (b : Bool) :
    (arithmeticSecondResidualLiftRetainedFactor hπ data H j hj u hu 2 b).toAlgHom.toRingHom =
      (arithmeticSecondResidualRetainedFactor hπ data H j hj u hu b).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id Q) (correctionSmoothing R π 2 τ (N b)) τ
          (arithmeticSecondRetainedSmoothing hπ data H j hj u hu 2 b)) := by
  have h := correctionNodeFactor_higher_eq R π 2 1 τ
    (arithmeticSecondSmoothing_annihilated data H)
    (reciprocalField (nonpositivePart (q b)))
  rw [correctionField_reciprocal, arithmeticSecondResidualIntegralField_spec] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
