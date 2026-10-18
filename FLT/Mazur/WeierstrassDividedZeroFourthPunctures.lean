/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthAnnihilation

/-!
# Full fourth punctures on the third corrected depth-zero smoothings

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
local notation "tA" => arithmeticZeroThirdInitialSmoothing hπ data H j hj u hu 4
local notation "tL" => arithmeticZeroThirdLastSmoothing hπ data H j hj u hu 4
local notation "tT" => arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu 4
local notation "A" => arithmeticZeroFourthInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroFourthLastIntegralField hπ data H j hj u hu
local notation "q" => arithmeticZeroFourthField hπ data H j hj u hu

/-- The actual initial outgoing substitution realizes the complete reciprocal field. -/
theorem arithmeticZeroFourthInitialPuncture_fourth (b : Bool) :
    correctionPunctureFactor R π 4 (tA b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 4 ^ 4)
        (nextCorrectionParameter_square R π 3) (reciprocalField (nonpositivePart (q false b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 4 _ (A b) true (T 1) = _
  rw [arithmeticZeroFourthInitialIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticZeroFourthInitialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticZeroFourthInitialField_boundary hπ data H j hj u hu b

/-- Both chosen fields are realized by the two punctures of the same whole last node. -/
theorem arithmeticZeroFourthLastPuncture_fourth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 4 (tL b) (V b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 4 ^ 4)
        (nextCorrectionParameter_square R π 3)
        (correctionField R π 4 (arithmeticZeroFourthLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 4 3
    (nextCorrectionParameter_square R π 3) _
    (arithmeticZeroFourthLastInput_annihilated hπ data H j hj u hu 4 b) _
    (arithmeticZeroFourthLastField_boundary hπ data H j hj u hu b) a

/-- The common terminal realizes both full positive closing fields on its prior smoothing. -/
theorem arithmeticZeroFourthTerminalPuncture_fourth (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π 4 tT
        (arithmeticZeroFourthTerminalIntegralField hπ data H j hj u hu) b =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 4 ^ 4)
        (nextCorrectionParameter_square R π 3) (positivePart (q true b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π 4 3
    (nextCorrectionParameter_square R π 3) tT
    (arithmeticZeroFourthTerminalInput_annihilated hπ data H j hj u hu 4)
    (arithmeticZeroFourthTerminalField hπ data H j hj u hu)
    (arithmeticZeroFourthTerminalField_boundary hπ data H j hj u hu) b
  rw [arithmeticZeroFourthTerminalField_spec] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
