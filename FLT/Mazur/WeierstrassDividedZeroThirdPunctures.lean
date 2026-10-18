/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdAnnihilation

/-!
# Full third punctures on the second corrected depth-zero smoothings

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
local notation "tA" => arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu 3
local notation "tL" => arithmeticZeroSecondLastSmoothing hπ data H j hj u hu 3
local notation "tT" => arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu 3
local notation "A" => arithmeticZeroThirdInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroThirdLastIntegralField hπ data H j hj u hu
local notation "q" => arithmeticZeroThirdField hπ data H j hj u hu

/-- The actual initial outgoing substitution realizes the complete reciprocal field. -/
theorem arithmeticZeroThirdInitialPuncture_third (b : Bool) :
    correctionPunctureFactor R π 3 (tA b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 3 ^ 3)
        (nextCorrectionParameter_square R π 2) (reciprocalField (nonpositivePart (q false b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 3 _ (A b) true (T 1) = _
  rw [arithmeticZeroThirdInitialIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticZeroThirdInitialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticZeroThirdInitialField_boundary hπ data H j hj u hu b

/-- Both chosen fields are realized by the two punctures of the same whole last node. -/
theorem arithmeticZeroThirdLastPuncture_third (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 3 (tL b) (V b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 3 ^ 3)
        (nextCorrectionParameter_square R π 2)
        (correctionField R π 3 (arithmeticZeroThirdLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 3 2
    (nextCorrectionParameter_square R π 2) _
    (arithmeticZeroThirdLastInput_annihilated hπ data H j hj u hu 3 b) _
    (arithmeticZeroThirdLastField_boundary hπ data H j hj u hu b) a

/-- The common terminal realizes both full positive closing fields on its prior smoothing. -/
theorem arithmeticZeroThirdTerminalPuncture_third (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π 3 tT
        (arithmeticZeroThirdTerminalIntegralField hπ data H j hj u hu) b =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 3 ^ 3)
        (nextCorrectionParameter_square R π 2) (positivePart (q true b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π 3 2
    (nextCorrectionParameter_square R π 2) tT
    (arithmeticZeroThirdTerminalInput_annihilated hπ data H j hj u hu 3)
    (arithmeticZeroThirdTerminalField hπ data H j hj u hu)
    (arithmeticZeroThirdTerminalField_boundary hπ data H j hj u hu) b
  rw [arithmeticZeroThirdTerminalField_spec] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
