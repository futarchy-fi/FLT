/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondResidualAlgebra
public import FLT.Mazur.WeierstrassDividedResidualLiftRestriction

/-!
# Original coefficient squares after the second residual correction

Both retained punctures, both terminal substitutions, and the complete new
closing residual follow the same adjacent arithmetic restriction. Composition
retains the two scalar drifts and all Laurent terms.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "A" => fun k ↦ arithmeticSecondResidualLiftRetainedPuncture hπ data H k j hj u hu
local notation "S" => fun k ↦ arithmeticSecondResidualLiftTerminalPuncture hπ data H k j hj u hu
local notation "K" => fun k ↦ arithmeticSecondResidualLiftEdgeEquiv hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticSecondResidualClosingEquiv hπ data H k j hj u hu

/-- Both full punctures of each retained correction preserve original coefficients. -/
theorem arithmeticSecondResidualLiftRetainedPuncture_restriction (b a : Bool) :
    (coeffMap f).comp (A (m + 1) b a).toAlgHom.toRingHom =
      (A m b a).toAlgHom.toRingHom.comp (coeffMap f) :=
  correctionPunctureFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a

/-- Both terminal punctures retain the quotient square after rebasing by the full drift. -/
theorem arithmeticSecondResidualLiftTerminalPuncture_restriction (b : Bool) :
    (coeffMap f).comp (S (m + 1) b).toAlgHom.toRingHom =
      (S m b).toAlgHom.toRingHom.comp (coeffMap f) :=
  twoBranchCorrectionRebasedPunctureFactor_restriction R π m _ _
    (arithmeticSecondResidualInputSmoothing_restriction hπ data H j hj u hu m) _ b

/-- Inverse-coordinate conjugation preserves both retained edge quotient squares. -/
theorem arithmeticSecondResidualLiftEdgeEquiv_restriction (b a : Bool) :
    (coeffMap f).comp (K (m + 1) b a).toAlgHom.toRingHom =
      (K m b a).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticSecondResidualLiftEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact arithmeticSecondResidualLiftRetainedPuncture_restriction hπ data H m j hj u hu b a
  · exact punctureEquiv_invert_naturality f

/-- The complete corrected closing residual follows the original adjacent coefficient map. -/
theorem arithmeticSecondResidualClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toAlgHom.toRingHom =
      (E m b).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticSecondResidualClosingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact symm_naturality f _ _
        (arithmeticSecondResidualLiftTerminalPuncture_restriction hπ data H m j hj u hu b)
    · exact arithmeticResidualLiftClosingEquiv_restriction hπ data H m j hj u hu b
  · exact symm_naturality f _ _
      (arithmeticSecondResidualLiftEdgeEquiv_restriction hπ data H m j hj u hu b true)

/-- The full inverse closing residual has the same adjacent coefficient square. -/
theorem arithmeticSecondResidualClosingEquiv_symm_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).symm.toAlgHom.toRingHom =
      (E m b).symm.toAlgHom.toRingHom.comp (coeffMap f) :=
  symm_naturality f _ _
    (arithmeticSecondResidualClosingEquiv_restriction hπ data H m j hj u hu b)

/-- The complete incoming transition preserves coefficients, including the old incoming error. -/
theorem arithmeticSecondResidualIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp
        (arithmeticSecondResidualIncomingEquiv
          hπ data H (m + 1) j hj u hu b).toAlgHom.toRingHom =
      (arithmeticSecondResidualIncomingEquiv
        hπ data H m j hj u hu b).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticSecondResidualIncomingEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticSecondResidualLiftEdgeEquiv_restriction hπ data H m j hj u hu b false
  · exact arithmeticResidualLiftEdgeEquiv_restriction hπ data H m j hj u hu b false

end FLT.Mazur.WeierstrassDividedDepth
