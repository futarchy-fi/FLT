/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthPairedFields
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Full fifth factors with two independently selected incident fields

The construction retains its entire input smoothing at every arithmetic order.
Its two punctures realize the selected residual projections at layer five.
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
  (out inc : FourthResidualEdge)
local notation "P" => arithmeticFifthPairedIntegralField hπ data H j hj u hu out inc
local notation "p" => arithmeticFifthPairedField hπ data H j hj u hu out inc

/-- The full new smoothing keeps both incident corrections and the complete old parameter. -/
def arithmeticFifthPairedSmoothing (m : ℕ) (s : Quotient R π m) (b : Bool) : Quotient R π m :=
  twoBranchCorrectionSmoothing R π m s (P b)

/-- One whole-node factor realizes both selected incident fields. -/
def arithmeticFifthPairedFactor (m : ℕ) (s : Quotient R π m) (b : Bool) :
    ChartRing (arithmeticFifthPairedSmoothing hπ data H j hj u hu out inc m s b) ≃ₐ[
      Quotient R π m] ChartRing s := twoBranchCorrectionNodeFactor R π m s (P b)

/-- The exact smoothing drift comes from the outgoing linear coefficient alone. -/
theorem arithmeticFifthPairedSmoothing_eq (m : ℕ) (s : Quotient R π m) (b : Bool) :
    arithmeticFifthPairedSmoothing hπ data H j hj u hu out inc m s b =
      (1 + parameter R π m ^ 5 * algebraMap R (Quotient R π m)
        ((p b true).coeff 1)) * s := by
  have hi : correctionSmoothing R π m s (P b false) = s := by
    rw [correctionSmoothing, arithmeticFifthPairedIntegralField, higherCorrectionField_coeff,
      arithmeticFifthPairedField_incoming_linear, mul_zero, map_zero, mul_zero,
      add_zero, one_mul]
  rw [arithmeticFifthPairedSmoothing, twoBranchCorrectionSmoothing, hi,
    arithmeticFifthPairedIntegralField, correctionSmoothing_higher]

/-- Both full punctures retain the old and new node parameters. -/
theorem arithmeticFifthPairedFactor_puncture (m : ℕ) (s : Quotient R π m) (b a : Bool) :
    (punctureLaurentMap s a).comp
        (arithmeticFifthPairedFactor hπ data H j hj u hu out inc m s b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m s (P b) a).toAlgHom.comp
        (punctureLaurentMap
          (arithmeticFifthPairedSmoothing hπ data H j hj u hu out inc m s b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m s (P b) a

/-- Both fifth punctures are their complete chosen finite fields. -/
theorem arithmeticFifthPairedPuncture_fifth (s : Quotient R π 5)
    (hs : parameter R π 5 ^ 5 * s = 0) (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5 s (P b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4) (correctionField R π 5 (p b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 5 4
    (nextCorrectionParameter_square R π 4) s hs _
    (arithmeticFifthPairedField_boundary hπ data H j hj u hu out inc b) a

/-- At the fifth layer the new smoothing equals the full previous smoothing. -/
theorem arithmeticFifthPairedSmoothing_fifth (s : Quotient R π 5)
    (hs : parameter R π 5 ^ 5 * s = 0) (b : Bool) :
    arithmeticFifthPairedSmoothing hπ data H j hj u hu out inc 5 s b = s :=
  twoBranchCorrectionSmoothing_higher_eq R π 5 4 s hs (p b)

end FLT.Mazur.WeierstrassDividedDepth
