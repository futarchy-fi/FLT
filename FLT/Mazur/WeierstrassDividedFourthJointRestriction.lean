/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthJointNodes

/-!
# Exact coefficient restrictions for the fourth full node factors

The predecessor retains its previous drifts in both coordinates, and the
common terminal retains the original restriction of its third smoothing.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "s" => fun k ↦ arithmeticThirdPrecedingSmoothing hπ data H j hj u hu k
local notation "P" => fun k ↦ arithmeticFourthPrecedingSmoothing hπ data H j hj u hu k
local notation "E" => fun k ↦ arithmeticFourthEarlierSmoothing hπ data H j hj u hu k
local notation "T" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu
local notation "t" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu
local notation "a" => fun k ↦ arithmeticThirdEarlierSmoothing hπ data H j hj u hu k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- The predecessor's new exact smoothing respects the original arithmetic quotient. -/
theorem arithmeticFourthPrecedingSmoothing_restriction (b : Bool) :
    restriction R π m (P (m + 1) b) = P m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b) _

/-- The earlier node retains the original full coefficient quotient on its new smoothing. -/
theorem arithmeticFourthEarlierSmoothing_restriction (b : Bool) :
    restriction R π m (E (m + 1) b) = E m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- The terminal retains both old scalar drifts and both new scalar drifts under restriction. -/
theorem arithmeticFourthTerminalSmoothing_restriction : restriction R π m (T (m + 1)) = T m :=
  twoBranchCorrectionRebasedSmoothing_restriction R π m _ _
    (arithmeticThirdTerminalSmoothing_restriction hπ data H j hj u hu m) _

local notation "N" => fun k ↦ arithmeticFourthPrecedingFactor hπ data H j hj u hu k
local notation "A" => fun k ↦ arithmeticFourthEarlierFactor hπ data H j hj u hu k
local notation "F" => arithmeticFourthTerminalFactor hπ data H j hj u hu

local notation "V" => arithmeticFourthLastIntegralField hπ data H j hj u hu
local notation "L" => fun k b ↦ twoBranchCorrectionSmoothing R π k (τ k) (V b)
local notation "C" => fun k ↦ arithmeticFourthLastFactor hπ data H j hj u hu k

/-- The full last-node factor also retains the explicit coefficient square on both coordinates. -/
theorem arithmeticFourthLastFactor_restriction (b : Bool) :
    (ringMap f (τ (m + 1)) (τ m)
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
        (C (m + 1) b).toAlgHom.toRingHom =
      (C m b).toAlgHom.toRingHom.comp (ringMap f (L (m + 1) b) (L m b)
        (twoBranchCorrectionSmoothing_restriction R π m _ _
          (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) (V b))) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) (V b)

/-- The whole predecessor factor commutes with explicit coefficient restriction on both nodes. -/
theorem arithmeticFourthPrecedingFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (P (m + 1) b) (P m b)
        (arithmeticFourthPrecedingSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b) _

/-- The entire earlier factor, including its opposite coordinate, keeps the original square. -/
theorem arithmeticFourthEarlierFactor_restriction (b : Bool) :
    (ringMap f (a (m + 1) b) (a m b)
      (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b)).comp
        (A (m + 1) b).toAlgHom.toRingHom =
      (A m b).toAlgHom.toRingHom.comp (ringMap f (E (m + 1) b) (E m b)
        (arithmeticFourthEarlierSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both terminal coordinates retain the exact quotient square of the rebased full factor. -/
theorem arithmeticFourthTerminalFactor_restriction :
    (ringMap f (T (m + 1)) (T m)
      (arithmeticFourthTerminalSmoothing_restriction hπ data H j hj u hu m)).comp
        (F (m + 1)).toAlgHom.toRingHom =
      (F m).toAlgHom.toRingHom.comp (ringMap f (t (m + 1)) (t m)
        (arithmeticThirdTerminalSmoothing_restriction hπ data H j hj u hu m)) :=
  twoBranchCorrectionRebasedFactor_restriction R π m _ _
    (arithmeticThirdTerminalSmoothing_restriction hπ data H j hj u hu m) _

end FLT.Mazur.WeierstrassDividedDepth
