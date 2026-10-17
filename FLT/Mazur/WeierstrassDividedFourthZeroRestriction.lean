/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroResidual
public import FLT.Mazur.WeierstrassDividedInitialBaseRestriction
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasRestriction
public import FLT.Mazur.WeierstrassDividedFourthNodeRestriction
public import FLT.Mazur.WeierstrassDividedFifthDeepEndInputRestriction

/-!
# Full coefficient quotients for the depth-zero initial residual

Both direct punctures retain the entire four-factor comparison under the
original arithmetic quotients. The initial source stays the original open.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "A" => fun k ↦ arithmeticFourthAccumulatedLastPuncture hπ data H k j hj u hu
local notation "E" => fun k ↦ arithmeticFourthZeroInitialEquiv hπ data H k j hj u hu
local notation "D" => fun k ↦ arithmeticFourthZeroInitialRelativeEquiv hπ data H k j hj u hu
local notation "C" => fun k ↦ arithmeticFourthAccumulatedLastIso hπ data H k j hj u hu
local notation "ρ" => closingNormalizedRestriction data H m

/-- Both accumulated direct punctures commute with the full coefficient quotient. -/
theorem arithmeticFourthAccumulatedLastPuncture_restriction (b a : Bool) :
    (coeffMap f).comp (A (m + 1) b a).toRingHom =
      (A m b a).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthAccumulatedLastPuncture
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · apply punctureEquiv_trans_naturality
      · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
          (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a
      · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
          (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a
  · exact arithmeticResidualLiftRetainedPuncture_restriction hπ data H m j hj u hu b a

/-- The entire original base and every last factor respect the same quotient square. -/
theorem arithmeticFourthZeroInitialEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthZeroInitialEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticFourthAccumulatedLastPuncture_restriction hπ data H j hj u hu m b false
  · exact arithmeticInitialBaseEquiv_restriction data H m j hj

/-- Measuring relative to the full original base preserves coefficient naturality. -/
theorem arithmeticFourthZeroInitialRelativeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toRingHom =
      (D m b).toRingHom.comp (coeffMap f) := by
  dsimp only
  rw [arithmeticFourthZeroInitialRelativeEquiv_eq, arithmeticFourthZeroInitialRelativeEquiv_eq]
  exact arithmeticFourthAccumulatedLastPuncture_restriction hπ data H j hj u hu m b false

/-- The complete accumulated last-node comparison preserves the full normalized quotient. -/
@[reassoc] theorem arithmeticFourthAccumulatedLastIso_restriction (b : Bool) :
    ρ ≫ (C (m + 1) b).hom = (C m b).hom ≫ ρ := by
  simp only [arithmeticFourthAccumulatedLastIso, Iso.trans_hom, Category.assoc]
  rw [arithmeticResidualLiftOrientedIso_restriction_assoc,
    arithmeticSecondJointOrientedIso_restriction_assoc,
    arithmeticThirdLastOrientedIso_restriction_assoc,
    arithmeticFourthLastOrientedIso_restriction]

variable [IsBezout R] (ha : 0 = j)
local notation "J" => fun k ↦
  arithmeticFourthOuterInitialZeroIdentification hπ data H k j hj u hu ha
local notation "S" => arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu

/-- The depth-zero initial input keeps the exact original full-open coefficient quotient. -/
@[reassoc] theorem arithmeticFourthZeroInitialInput_restriction (b : Bool) :
    (J m b).hom ≫ S m (.initial b) =
      arithmeticFullInitialNodeQuotient R π m W (π ^ 1) ≫ (J (m + 1) b).hom := by
  apply (cancel_mono
    (arithmeticFourthOuterAtlasChart hπ data H (m + 1) j hj u hu (.initial b))).mp
  rw [Category.assoc, arithmeticFourthOuterAtlasChart_restriction,
    ← Category.assoc, arithmeticFourthOuterAtlasChart_initial_zero,
    Category.assoc, arithmeticFourthOuterAtlasChart_initial_zero]
  have h := arithmeticThirdAtlasChart_restriction hπ data H j hj u hu m (.initial b)
  rw [arithmeticThirdAtlasRestriction_initial] at h
  exact h.symm

end FLT.Mazur.WeierstrassDividedDepth
