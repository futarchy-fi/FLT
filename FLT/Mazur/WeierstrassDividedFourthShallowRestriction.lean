/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowCancellation
public import FLT.Mazur.WeierstrassDividedFourthResidualRestriction

/-!
# Full coefficient squares for the fourth initial corrections

Both new smoothings, the whole node factors and both incident edge residuals
retain the original arithmetic coefficient quotients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "a" => fun m (_ : Bool) ↦
  arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu
local notation "A" => arithmeticFourthShallowSmoothing hπ data H j hj u hu
local notation "S" => arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFourthShallowFactor hπ data H j hj u hu
local notation "P" => arithmeticFourthShallowNeighborFactor hπ data H j hj u hu
local notation "E" => arithmeticFourthShallowEquiv hπ data H j hj u hu
local notation "I" => arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu

/-- The initial node's full new smoothing is compatible with the original quotient. -/
theorem arithmeticFourthShallowSmoothing_restriction (b : Bool) :
    restriction R π m (A (m + 1) b) = A m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- Both new earlier neighbor drifts survive the same full coefficient restriction. -/
theorem arithmeticFourthShallowNeighborSmoothing_restriction (b : Bool) :
    restriction R π m (S (m + 1) b) = S m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- The whole initial node factor retains the quotient square on both coordinates. -/
theorem arithmeticFourthShallowFactor_restriction (b : Bool) :
    (ringMap f (a (m + 1) b) (a m b)
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (A (m + 1) b) (A m b)
        (arithmeticFourthShallowSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- Both neighboring coordinates use their exact old and new coefficient quotients. -/
theorem arithmeticFourthShallowNeighborFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b)).comp
        (P (m + 1) b).toAlgHom.toRingHom =
      (P m b).toAlgHom.toRingHom.comp (ringMap f (S (m + 1) b) (S m b)
        (arithmeticFourthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- The full corrected initial residual retains every original coefficient square. -/
theorem arithmeticFourthShallowEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthShallowEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _ false
    · apply punctureEquiv_trans_naturality
      · exact arithmeticThirdEarlierOppositeEquiv_restriction hπ data H j hj u hu m b
      · exact arithmeticInitialBaseEquiv_restriction data H m j hj
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ true

/-- The shared residual uses the same full corrected earlier neighbor under restriction. -/
theorem arithmeticFourthShallowNeighborIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (I (m + 1) b).toRingHom =
      (I m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthShallowNeighborIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFourthPrecedingEdgeEquiv_restriction hπ data H j hj u hu m b
    · exact arithmeticThirdPrecedingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
