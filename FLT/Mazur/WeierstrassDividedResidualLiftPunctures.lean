/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCorrectionPunctures
public import FLT.Mazur.PolygonSmoothingPunctureGeometry
public import FLT.Mazur.WeierstrassDividedResidualLiftGeometry

/-!
# Full geometric punctures of the actual lifted residual corrections

The terminal inverse uses the rebased two-branch substitution. Each retained
node has two full puncture substitutions, including its affected incoming
branch. These are the actual geometric corrections used by the lifted atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu

/-- The full rebased terminal puncture substitution before geometric inversion. -/
def arithmeticResidualLiftTerminalPuncture (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  twoBranchCorrectionRebasedPunctureFactor R π m σ
    (arithmeticTerminalIntegralField hπ data H j hj u hu) b

/-- Each actual retained integral field supplies both complete puncture substitutions. -/
def arithmeticResidualLiftRetainedPuncture (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  correctionPunctureFactor R π m τ (arithmeticRetainedIntegralField hπ data H j hj u hu b) a

local notation "S" => arithmeticResidualLiftTerminalPuncture hπ data H m j hj u hu
local notation "A" => arithmeticResidualLiftRetainedPuncture hπ data H m j hj u hu
local notation "F" => arithmeticResidualLiftTerminalIso hπ data H m j hj u hu
local notation "K" => arithmeticResidualLiftRetainedIso hπ data H m j hj u hu

/-- The actual inverse terminal chart correction uses the entire inverse Laurent factor. -/
@[reassoc] theorem arithmeticResidualLiftTerminalIso_puncture (b : Bool) :
    punctureOpen σ b ≫ (F).hom = (punctureSpecIso (S b).symm).hom ≫ punctureOpen s b := by
  unfold arithmeticResidualLiftTerminalIso arithmeticResidualLiftTerminalPuncture
    arithmeticResidualLiftTerminalSmoothing
  exact punctureFactor_spec _ _
    (twoBranchCorrectionRebasedFactor R π m σ
      (arithmeticTerminalIntegralField hπ data H j hj u hu)).symm
    (twoBranchCorrectionRebasedPunctureFactor R π m σ
      (arithmeticTerminalIntegralField hπ data H j hj u hu) b).symm b
    (twoBranchCorrectionRebasedFactor_symm_puncture R π m σ _ b)

/-- Normalizing the retained smoothing preserves both full puncture substitutions. -/
@[reassoc] theorem arithmeticResidualLiftRetainedIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (K b).hom = (punctureSpecIso (A b a)).hom ≫ punctureOpen τ a := by
  apply punctureFactor_spec_normalized
  rw [arithmeticResidualRetainedLift_def]
  exact correctionNodeFactor_puncture R π m τ _ a

/-- Both labeled retained punctures retain their full substitutions after orientation. -/
@[reassoc] theorem arithmeticResidualLiftOrientedIso_puncture (b a : Bool) :
    (punctureOpen τ a ≫ (twistedRetainedOrientation data H m b).hom) ≫
        (arithmeticResidualLiftOrientedIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (A b a)).hom ≫ punctureOpen τ a ≫
        (twistedRetainedOrientation data H m b).hom := by
  rw [Category.assoc, arithmeticResidualLiftOrientedIso_hom,
    ← Category.assoc, arithmeticResidualLiftRetainedIso_puncture, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
