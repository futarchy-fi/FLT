/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdJointNodes

/-!
# Exact coefficient restrictions for the third full node factors

The predecessor retains its previous drift in both coordinates, and the
common terminal retains the original restriction of its second smoothing.
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
local notation "s" => fun k ↦ arithmeticSecondPrecedingSmoothing hπ data H k j hj u hu
local notation "P" => fun k ↦ arithmeticThirdPrecedingSmoothing hπ data H j hj u hu k
local notation "E" => fun k ↦ arithmeticThirdEarlierSmoothing hπ data H j hj u hu k
local notation "T" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu
local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- The predecessor's new exact smoothing respects the original arithmetic quotient. -/
theorem arithmeticThirdPrecedingSmoothing_restriction (b : Bool) :
    restriction R π m (P (m + 1) b) = P m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticSecondPrecedingSmoothing_restriction hπ data H m j hj u hu b) _

/-- The earlier node retains the original full coefficient quotient on its new smoothing. -/
theorem arithmeticThirdEarlierSmoothing_restriction (b : Bool) :
    restriction R π m (E (m + 1) b) = E m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- The terminal retains both old scalar drifts and both new scalar drifts under restriction. -/
theorem arithmeticThirdTerminalSmoothing_restriction : restriction R π m (T (m + 1)) = T m :=
  twoBranchCorrectionRebasedSmoothing_restriction R π m _ _
    (arithmeticSecondResidualLiftSmoothing_restriction hπ data H j hj u hu m) _

local notation "N" => fun k ↦ arithmeticThirdPrecedingFactor hπ data H j hj u hu k
local notation "A" => fun k ↦ arithmeticThirdEarlierFactor hπ data H j hj u hu k
local notation "F" => arithmeticThirdTerminalFactor hπ data H j hj u hu

local notation "V" => arithmeticThirdLastIntegralField hπ data H j hj u hu
local notation "L" => fun k b ↦ twoBranchCorrectionSmoothing R π k (τ k) (V b)
local notation "C" => fun k ↦ arithmeticThirdLastFactor hπ data H j hj u hu k

/-- The full last-node factor also retains the explicit coefficient square on both coordinates. -/
theorem arithmeticThirdLastFactor_restriction (b : Bool) :
    (ringMap f (τ (m + 1)) (τ m)
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
        (C (m + 1) b).toAlgHom.toRingHom =
      (C m b).toAlgHom.toRingHom.comp (ringMap f (L (m + 1) b) (L m b)
        (twoBranchCorrectionSmoothing_restriction R π m _ _
          (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) (V b))) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) (V b)

/-- The whole predecessor factor commutes with explicit coefficient restriction on both nodes. -/
theorem arithmeticThirdPrecedingFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticSecondPrecedingSmoothing_restriction hπ data H m j hj u hu b)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (P (m + 1) b) (P m b)
        (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticSecondPrecedingSmoothing_restriction hπ data H m j hj u hu b) _

/-- The entire earlier factor, including its opposite coordinate, keeps the original square. -/
theorem arithmeticThirdEarlierFactor_restriction (b : Bool) :
    (ringMap f (τ (m + 1)) (τ m)
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
        (A (m + 1) b).toAlgHom.toRingHom =
      (A m b).toAlgHom.toRingHom.comp (ringMap f (E (m + 1) b) (E m b)
        (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- Both terminal coordinates retain the exact quotient square of the rebased full factor. -/
theorem arithmeticThirdTerminalFactor_restriction :
    (ringMap f (T (m + 1)) (T m)
      (arithmeticThirdTerminalSmoothing_restriction hπ data H j hj u hu m)).comp
        (F (m + 1)).toAlgHom.toRingHom =
      (F m).toAlgHom.toRingHom.comp (ringMap f (t (m + 1)) (t m)
        (arithmeticSecondResidualLiftSmoothing_restriction hπ data H j hj u hu m)) :=
  twoBranchCorrectionRebasedFactor_restriction R π m _ _
    (arithmeticSecondResidualLiftSmoothing_restriction hπ data H j hj u hu m) _

end FLT.Mazur.WeierstrassDividedDepth
