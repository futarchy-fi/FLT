/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEndCancellation
public import FLT.Mazur.WeierstrassDividedFifthDeepRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowResidualRestriction
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Full coefficient squares at both ends of the fifth outer chain

The next earlier smoothing and full node factor retain their original quotient.
The shared incoming and farther incoming residuals retain all three full maps.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthIncomingEquiv arithmeticFourthFartherIncomingEquiv
  arithmeticFifthPairedIntegralField arithmeticFifthShallowLastEdgeEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFifthDeepEarlierFactor hπ data H j hj u hu
local notation "A" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu
variable (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- The next earlier node retains the full quotient of its new exact scalar drift. -/
theorem arithmeticFifthDeepEarlierSmoothing_restriction (b : Bool) :
    restriction R π m (s (m + 1) b) = s m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- The earlier whole-node factor retains both coordinate quotient squares. -/
theorem arithmeticFifthDeepEarlierFactor_restriction (b : Bool) :
    (ringMap f (τ (m + 1)) (τ m)
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (s (m + 1) b) (s m b)
        (arithmeticFifthDeepEarlierSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- Both full earlier punctures respect the original arithmetic coefficient map. -/
theorem arithmeticFifthDeepEarlierPuncture_restriction (b a : Bool) :
    (coeffMap f).comp (correctionPunctureFactor R π (m + 1) (τ (m + 1)) (A b) a).toRingHom =
      (correctionPunctureFactor R π m (τ m) (A b) a).toRingHom.comp (coeffMap f) :=
  correctionPunctureFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a

/-- The shared incoming residual respects the complete quotient square at every order. -/
theorem arithmeticFifthDeepIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp
        (arithmeticFifthDeepIncomingEquiv hπ data H j hj u hu (m + 1) b).toRingHom =
      (arithmeticFifthDeepIncomingEquiv hπ data H j hj u hu m b).toRingHom.comp
        (coeffMap f) := by
  unfold arithmeticFifthDeepIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFifthShallowLastEdgeEquiv_restriction hπ data H j hj u hu m b false
    · exact arithmeticFourthIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFifthDeepInput_restriction hπ data H j hj u hu .predecessor m b) _ true

/-- The full farther residual keeps the same quotient on its complete old compensation. -/
theorem arithmeticFifthDeepFartherIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp
        (arithmeticFifthDeepFartherIncomingEquiv hπ data H j hj u hu (m + 1) b).toRingHom =
      (arithmeticFifthDeepFartherIncomingEquiv hπ data H j hj u hu m b).toRingHom.comp
        (coeffMap f) := by
  unfold arithmeticFifthDeepFartherIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFifthDeepEdgeEquiv_restriction hπ data H j hj u hu m .farther b
    · exact arithmeticFourthFartherIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ true

end FLT.Mazur.WeierstrassDividedDepth
