/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureSpecNaturality
public import FLT.Mazur.WeierstrassDividedTerminalChangedRestriction
public import FLT.Mazur.WeierstrassDividedTerminalResidualAlgebra

/-!
# Full coefficient squares for the original terminal residual

Cancel the original open puncture from the complete changed-boundary square.
Faithfulness of spectrum then gives the coefficient square on all functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "σ" => fun k ↦ arithmeticTerminalChangedSmoothing data H k j hj u hu
local notation "D" => fun k ↦ arithmeticTerminalResidualTwist data H k j hj u hu
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "S" => arithmeticTerminalChangedRestriction hπ data H m j hj u hu

include hπ

/-- The complete terminal residual preserves the original adjacent coefficient arrow. -/
@[reassoc] theorem arithmeticTerminalResidualTwist_restriction (b : Bool) :
    (D m b).hom ≫ ρ = ρ ≫ (D (m + 1) b).hom := by
  have hp (k : ℕ) :
      (if b then leftBranchOpen (Quotient R π k) (σ k)
        else rightBranchOpen (Quotient R π k) (σ k)) = punctureOpen (σ k) b := by
    cases b
    · exact (punctureOpen_false _).symm
    · exact (punctureOpen_true _).symm
  have h := arithmeticTerminalChangedBoundary_restriction hπ data H m j hj u hu b
  simp only [arithmeticTerminalChangedBoundary, hp, Category.assoc] at h
  have hs : punctureOpen (σ m) b ≫ S = ρ ≫ punctureOpen (σ (m + 1)) b :=
    punctureOpen_ringMap _ _ _
      (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ) b
  rw [hs] at h
  let _ : Mono (punctureOpen (σ (m + 1)) b) := by
    cases b
    · rw [punctureOpen_false]
      infer_instance
    · rw [punctureOpen_true]
      infer_instance
  apply (cancel_mono (punctureOpen (σ (m + 1)) b)).mp
  simpa only [Category.assoc] using h

/-- Every original residual coefficient, including inverse terms, follows the quotient map. -/
theorem arithmeticTerminalResidualEquiv_restriction (b : Bool) :
    (coeffMap (restriction R π m).toRingHom).comp
        (arithmeticTerminalResidualEquiv data H (m + 1) j hj u hu b).toAlgHom.toRingHom =
      (arithmeticTerminalResidualEquiv data H m j hj u hu b).toAlgHom.toRingHom.comp
        (coeffMap (restriction R π m).toRingHom) := by
  apply (punctureSpecIso_naturality_iff _ _ _).mp
  have hs (k : ℕ) :
      (punctureSpecIso (arithmeticTerminalResidualEquiv data H k j hj u hu b)).hom =
        (D k b).hom := arithmeticTerminalResidualEquiv_spec data H k j hj u hu b
  rw [hs, hs]
  exact arithmeticTerminalResidualTwist_restriction hπ data H m j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
