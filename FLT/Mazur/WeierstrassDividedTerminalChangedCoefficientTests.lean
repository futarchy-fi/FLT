/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalResidualAlgebra

/-!
# Full coefficient tests for the changed terminal gluing

Pull the full residual transition back through the original inverse terminal
parameter. Both resulting boundaries extend over the changed smoothing.
The coefficient tests are proved, with no tangent-only sufficiency assertion.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX PolygonScaledReciprocal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "a" => arithmeticTerminalTangentScale data H m j hj u hu
local notation "N" => arithmeticTerminalNormalizationEquiv data H m j hj u hu
local notation "D" => arithmeticTerminalResidualEquiv data H m j hj u hu
/-- A sealed full coordinate map avoids expanding the chosen inverse Laurent substitutions. -/
irreducible_def arithmeticTerminalChangedCoordinateMap : ChartRing σ →ₐ[Q] ChartRing τ :=
  changeParameter τ σ (a true) (a false) rfl

local notation "C" => arithmeticTerminalChangedCoordinateMap data H m j hj u hu

/-- The actual inverse source parameter followed by the full residual target transition. -/
irreducible_def arithmeticTerminalChangedPullback (b : Bool) : ChartRing σ →ₐ[Q] L :=
  (N b).toAlgHom.comp ((D b).toAlgHom.comp
    (if b then leftLaurentMap σ else (leftLaurentMap σ).comp (branchSwapMap σ)))

local notation "F" => arithmeticTerminalChangedPullback data H m j hj u hu

/-- The entire revised boundary, including its inverse Laurent terms, has the specified scale. -/
theorem arithmeticTerminalChangedPullback_eq (b : Bool) :
    F b = (scaling (a b)).comp
      (if b then leftLaurentMap σ else (leftLaurentMap σ).comp (branchSwapMap σ)) := by
  rw [arithmeticTerminalChangedPullback_def]
  apply AlgHom.ext
  intro z
  exact (N b).apply_symm_apply _

/-- Both full revised boundaries are restrictions of the single constructed coordinate map. -/
theorem arithmeticTerminalChangedPullback_branch (b : Bool) :
    (if b then leftLaurentMap τ else (leftLaurentMap τ).comp (branchSwapMap τ)).comp C =
      F b := by
  rw [arithmeticTerminalChangedCoordinateMap_def, arithmeticTerminalChangedPullback_eq]
  cases b
  · exact rightLaurentMap_changeParameter ..
  · exact leftLaurentMap_changeParameter ..

/-- The full reconstructed coordinate map has an explicit inverse on the changed smoothing. -/
theorem arithmeticTerminalChangedCoordinateMap_bijective : Function.Bijective C := by
  rw [arithmeticTerminalChangedCoordinateMap_def]
  exact (changeParameterEquiv τ σ (a true) (a false) rfl).bijective

/-- All Laurent coefficients of both changed-coordinate candidates obey the exact tests. -/
theorem arithmeticTerminalChangedPullback_compatible :
    LaurentCompatible τ (F true (leftCoordinate σ))
        (LaurentPolynomial.invert (F false (leftCoordinate σ))) ∧
      LaurentCompatible τ (F true (rightCoordinate σ))
        (LaurentPolynomial.invert (F false (rightCoordinate σ))) := by
  apply (boundaryLift_exists_iff σ τ (F true)
    (LaurentPolynomial.invert.toAlgHom.comp (F false))).mp
  refine ⟨C, arithmeticTerminalChangedPullback_branch data H m j hj u hu true, ?_⟩
  have hr := congrArg (fun f : ChartRing σ →ₐ[Q] L ↦
    LaurentPolynomial.invert.toAlgHom.comp f)
    (arithmeticTerminalChangedPullback_branch data H m j hj u hu false)
  simpa only [Bool.false_eq_true, ↓reduceIte, precedingLaurentMap, AlgHom.comp_assoc] using hr

/-- The full coefficient reconstruction recovers the explicitly invertible changed-chart map. -/
theorem arithmeticTerminalChangedPullback_reconstruct :
    boundaryLift σ τ (F true) (LaurentPolynomial.invert.toAlgHom.comp (F false))
      (arithmeticTerminalChangedPullback_compatible data H m j hj u hu).1
      (arithmeticTerminalChangedPullback_compatible data H m j hj u hu).2 = C := by
  symm
  apply boundaryLift_unique
  · exact arithmeticTerminalChangedPullback_branch data H m j hj u hu true
  · have hr := congrArg (fun f : ChartRing σ →ₐ[Q] L ↦
      LaurentPolynomial.invert.toAlgHom.comp f)
      (arithmeticTerminalChangedPullback_branch data H m j hj u hu false)
    simpa only [Bool.false_eq_true, ↓reduceIte, precedingLaurentMap, AlgHom.comp_assoc] using hr

end FLT.Mazur.WeierstrassDividedDepth
