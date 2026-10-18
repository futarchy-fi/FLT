/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondAnnihilation

/-!
# Full second punctures on the first corrected depth-zero smoothings

The initial and last incoming punctures split the measured relative initial
error. The same last factor and common terminal split both closing errors.
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
local notation "tA" => arithmeticZeroFirstInitialSmoothing hπ data H j hj u hu 2
local notation "tL" => arithmeticZeroFirstLastSmoothing hπ data H j hj u hu 2
local notation "tT" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu 2
local notation "A" => arithmeticZeroSecondInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroSecondLastIntegralField hπ data H j hj u hu
local notation "q" => arithmeticZeroSecondField hπ data H j hj u hu

/-- The actual initial outgoing substitution realizes the complete reciprocal field. -/
theorem arithmeticZeroSecondInitialPuncture_second (b : Bool) :
    correctionPunctureFactor R π 2 (tA b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 2 ^ 2)
        (nextCorrectionParameter_square R π 1) (reciprocalField (nonpositivePart (q false b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 2 _ (A b) true (T 1) = _
  rw [arithmeticZeroSecondInitialIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticZeroSecondInitialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticZeroSecondInitialField_boundary hπ data H j hj u hu b

/-- Both chosen fields are realized by the two punctures of the same whole last node. -/
theorem arithmeticZeroSecondLastPuncture_second (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 2 (tL b) (V b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 2 ^ 2)
        (nextCorrectionParameter_square R π 1)
        (correctionField R π 2 (arithmeticZeroSecondLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 2 1
    (nextCorrectionParameter_square R π 1) _
    (arithmeticZeroSecondLastInput_annihilated hπ data H j hj u hu 2 b) _
    (arithmeticZeroSecondLastField_boundary hπ data H j hj u hu b) a

/-- The common terminal realizes both full positive closing fields on its prior smoothing. -/
theorem arithmeticZeroSecondTerminalPuncture_second (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π 2 tT
        (arithmeticZeroSecondTerminalIntegralField hπ data H j hj u hu) b =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 2 ^ 2)
        (nextCorrectionParameter_square R π 1) (positivePart (q true b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π 2 1
    (nextCorrectionParameter_square R π 1) tT
    (arithmeticZeroSecondTerminalInput_annihilated hπ data H j hj u hu 2)
    (arithmeticZeroSecondTerminalField hπ data H j hj u hu)
    (arithmeticZeroSecondTerminalField_boundary hπ data H j hj u hu) b
  rw [arithmeticZeroSecondTerminalField_spec] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
