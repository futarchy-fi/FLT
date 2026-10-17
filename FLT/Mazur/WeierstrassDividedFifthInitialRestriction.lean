/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialNodes
public import FLT.Mazur.WeierstrassDividedFourthInitialRestriction

/-!
# Full coefficient squares for the fifth initial corrections

Both new smoothings and both whole-node factors retain the original
arithmetic coefficient quotients of the full fourth depth-one inputs.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthInitialEquiv
  arithmeticFifthResidualIntegralField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "a" => arithmeticFourthInitialSmoothing hπ data H j hj u hu
local notation "s" => arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu
local notation "A" => arithmeticFifthInitialSmoothing hπ data H j hj u hu
local notation "S" => arithmeticFifthInitialNeighborSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFifthInitialFactor hπ data H j hj u hu
local notation "P" => arithmeticFifthInitialNeighborFactor hπ data H j hj u hu

/-- The initial node's full new smoothing is compatible with the original quotient. -/
theorem arithmeticFifthInitialSmoothing_restriction (b : Bool) :
    restriction R π m (A (m + 1) b) = A m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticFourthInitialSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both new earlier neighbor drifts survive the same full coefficient restriction. -/
theorem arithmeticFifthInitialNeighborSmoothing_restriction (b : Bool) :
    restriction R π m (S (m + 1) b) = S m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticFourthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b) _

/-- The whole initial node factor retains the quotient square on both coordinates. -/
theorem arithmeticFifthInitialFactor_restriction (b : Bool) :
    (ringMap f (a (m + 1) b) (a m b)
      (arithmeticFourthInitialSmoothing_restriction hπ data H j hj u hu m b)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (A (m + 1) b) (A m b)
        (arithmeticFifthInitialSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticFourthInitialSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both neighboring coordinates use their exact old and new coefficient quotients. -/
theorem arithmeticFifthInitialNeighborFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticFourthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b)).comp
        (P (m + 1) b).toAlgHom.toRingHom =
      (P m b).toAlgHom.toRingHom.comp (ringMap f (S (m + 1) b) (S m b)
        (arithmeticFifthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticFourthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b) _

end FLT.Mazur.WeierstrassDividedDepth
