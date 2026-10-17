/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstNodes

/-!
# Both full punctures of the first depth-zero correction

The initial and last incoming punctures realize the complementary measured
fields. The other puncture of that same last factor is identity at layer one.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "A" => arithmeticZeroFirstInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroFirstLastIntegralField hπ data H j hj u hu
local notation "q" => arithmeticFourthZeroFirstField hπ data H j hj u hu

/-- The actual initial outgoing substitution realizes the complete reciprocal field. -/
theorem arithmeticZeroFirstInitialPuncture_first (b : Bool) :
    correctionPunctureFactor R π 1 τ (A b) true =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 1 ^ 1)
        (nextCorrectionParameter_square R π 0) (reciprocalField (nonpositivePart (q b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 1 _ (A b) true (T 1) = _
  rw [arithmeticZeroFirstInitialIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticZeroFirstInitialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact arithmeticZeroFirstInitialField_boundary hπ data H j hj u hu b

/-- Both chosen fields are realized by the two punctures of the same whole last node. -/
theorem arithmeticZeroFirstLastPuncture_first (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 1 τ (V b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 1 ^ 1)
        (nextCorrectionParameter_square R π 0)
        (correctionField R π 1 (arithmeticZeroFirstLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 1 0
    (nextCorrectionParameter_square R π 0) _ (arithmeticTopSmoothing_annihilated data H 1) _
    (arithmeticZeroFirstLastField_boundary hπ data H j hj u hu b) a

/-- The same last factor makes no outgoing change at layer one. -/
theorem arithmeticZeroFirstLastPuncture_outgoing_first (b : Bool) :
    twoBranchCorrectionPunctureFactor R π 1 τ (V b) true = AlgEquiv.refl := by
  rw [arithmeticZeroFirstLastPuncture_first]
  apply AlgEquiv.coe_toAlgHom_injective
  change LaurentSquareZeroAutomorphism.subst _ _
    (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 1)) 0) = _
  rw [map_zero, LaurentSquareZeroAutomorphism.subst_zero]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
