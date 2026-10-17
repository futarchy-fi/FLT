/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftAlgebra
public import FLT.Mazur.WeierstrassDividedTerminalResidualRestriction
public import FLT.Mazur.PolygonArithmeticCorrectionPunctureRestriction

/-!
# Original coefficient squares of the recomputed full transitions

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
local notation "A" => fun k ↦ arithmeticResidualLiftRetainedPuncture hπ data H k j hj u hu
local notation "S" => fun k ↦ arithmeticResidualLiftTerminalPuncture hπ data H k j hj u hu
local notation "K" => fun k ↦ arithmeticResidualLiftEdgeEquiv hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticResidualLiftClosingEquiv hπ data H k j hj u hu

/-- Both full punctures of each retained correction preserve original coefficients. -/
theorem arithmeticResidualLiftRetainedPuncture_restriction (b a : Bool) :
    (coeffMap f).comp (A (m + 1) b a).toAlgHom.toRingHom =
      (A m b a).toAlgHom.toRingHom.comp (coeffMap f) :=
  correctionPunctureFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a

/-- Both terminal punctures retain the quotient square after rebasing by the full drift. -/
theorem arithmeticResidualLiftTerminalPuncture_restriction (b : Bool) :
    (coeffMap f).comp (S (m + 1) b).toAlgHom.toRingHom =
      (S m b).toAlgHom.toRingHom.comp (coeffMap f) :=
  twoBranchCorrectionRebasedPunctureFactor_restriction R π m _ _
    (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ) _ b

/-- Inverse-coordinate conjugation preserves both retained edge quotient squares. -/
theorem arithmeticResidualLiftEdgeEquiv_restriction (b a : Bool) :
    (coeffMap f).comp (K (m + 1) b a).toAlgHom.toRingHom =
      (K m b a).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticResidualLiftEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact arithmeticResidualLiftRetainedPuncture_restriction hπ data H m j hj u hu b a
  · exact punctureEquiv_invert_naturality f

/-- The complete corrected closing residual follows the original adjacent coefficient map. -/
theorem arithmeticResidualLiftClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toAlgHom.toRingHom =
      (E m b).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticResidualLiftClosingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact symm_naturality f _ _
        (arithmeticResidualLiftTerminalPuncture_restriction hπ data H m j hj u hu b)
    · exact arithmeticTerminalResidualEquiv_restriction hπ data H m j hj u hu b
  · exact symm_naturality f _ _
      (arithmeticResidualLiftEdgeEquiv_restriction hπ data H m j hj u hu b true)

/-- The full inverse closing residual has the same adjacent coefficient square. -/
theorem arithmeticResidualLiftClosingEquiv_symm_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).symm.toAlgHom.toRingHom =
      (E m b).symm.toAlgHom.toRingHom.comp (coeffMap f) :=
  symm_naturality f _ _
    (arithmeticResidualLiftClosingEquiv_restriction hπ data H m j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
