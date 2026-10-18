/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthAnnihilation

/-!
# Full fifth punctures on the fourth corrected depth-zero smoothings

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
local notation "tA" => arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu 5
local notation "tL" => arithmeticZeroFourthLastSmoothing hπ data H j hj u hu 5
local notation "tT" => arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu 5
local notation "A" => arithmeticZeroFifthInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroFifthLastIntegralField hπ data H j hj u hu
local notation "q" => arithmeticZeroFifthField hπ data H j hj u hu

/-- The actual initial outgoing substitution realizes the complete reciprocal field. -/
theorem arithmeticZeroFifthInitialPuncture_fifth (b : Bool) :
    correctionPunctureFactor R π 5 (tA b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4) (reciprocalField (nonpositivePart (q false b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 5 _ (A b) true (T 1) = _
  rw [arithmeticZeroFifthInitialIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticZeroFifthInitialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticZeroFifthInitialField_boundary hπ data H j hj u hu b

/-- Both chosen fields are realized by the two punctures of the same whole last node. -/
theorem arithmeticZeroFifthLastPuncture_fifth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5 (tL b) (V b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4)
        (correctionField R π 5 (arithmeticZeroFifthLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 5 4
    (nextCorrectionParameter_square R π 4) _
    (arithmeticZeroFifthLastInput_annihilated hπ data H j hj u hu 5 b) _
    (arithmeticZeroFifthLastField_boundary hπ data H j hj u hu b) a

/-- The common terminal realizes both full positive closing fields on its prior smoothing. -/
theorem arithmeticZeroFifthTerminalPuncture_fifth (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π 5 tT
        (arithmeticZeroFifthTerminalIntegralField hπ data H j hj u hu) b =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4) (positivePart (q true b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π 5 4
    (nextCorrectionParameter_square R π 4) tT
    (arithmeticZeroFifthTerminalInput_annihilated hπ data H j hj u hu 5)
    (arithmeticZeroFifthTerminalField hπ data H j hj u hu)
    (arithmeticZeroFifthTerminalField_boundary hπ data H j hj u hu) b
  rw [arithmeticZeroFifthTerminalField_spec] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
