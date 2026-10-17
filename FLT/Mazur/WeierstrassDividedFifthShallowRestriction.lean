/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowCancellation
public import FLT.Mazur.WeierstrassDividedFifthShallowResidualRestriction

/-!
# Full coefficient squares for the fifth initial corrections

Both new smoothings, the whole node factors and both incident edge residuals
retain the original arithmetic coefficient quotients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthShallowEquiv
  arithmeticFifthResidualIntegralField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "a" => arithmeticFourthShallowSmoothing hπ data H j hj u hu
local notation "s" => arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu
local notation "A" => arithmeticFifthShallowSmoothing hπ data H j hj u hu
local notation "S" => arithmeticFifthShallowNeighborSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFifthShallowFactor hπ data H j hj u hu
local notation "P" => arithmeticFifthShallowNeighborFactor hπ data H j hj u hu
local notation "E" => arithmeticFifthShallowEquiv hπ data H j hj u hu

/-- The initial node's full new smoothing is compatible with the original quotient. -/
theorem arithmeticFifthShallowSmoothing_restriction (b : Bool) :
    restriction R π m (A (m + 1) b) = A m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticFourthShallowSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both new earlier neighbor drifts survive the same full coefficient restriction. -/
theorem arithmeticFifthShallowNeighborSmoothing_restriction (b : Bool) :
    restriction R π m (S (m + 1) b) = S m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticFourthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b) _

/-- The whole initial node factor retains the quotient square on both coordinates. -/
theorem arithmeticFifthShallowFactor_restriction (b : Bool) :
    (ringMap f (a (m + 1) b) (a m b)
      (arithmeticFourthShallowSmoothing_restriction hπ data H j hj u hu m b)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (A (m + 1) b) (A m b)
        (arithmeticFifthShallowSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticFourthShallowSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both neighboring coordinates use their exact old and new coefficient quotients. -/
theorem arithmeticFifthShallowNeighborFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticFourthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b)).comp
        (P (m + 1) b).toAlgHom.toRingHom =
      (P m b).toAlgHom.toRingHom.comp (ringMap f (S (m + 1) b) (S m b)
        (arithmeticFifthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticFourthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b) _

/-- The full corrected initial residual retains every original coefficient square. -/
theorem arithmeticFifthShallowEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthShallowEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticFourthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b) _ false
    · exact arithmeticFourthShallowEquiv_restriction hπ data H j hj u hu m b
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFourthShallowSmoothing_restriction hπ data H j hj u hu m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
