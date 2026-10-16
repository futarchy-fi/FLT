/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalBoundaryExtension
public import FLT.Mazur.WeierstrassDividedClosedTerminalNormalization

/-!
# The constructed terminal extension recovers the closed normalization

At order zero the actual Laurent inverse substitutions are the previously
constructed independent scalings. This proves the coefficient tests there
and identifies the full new extension with that same original correction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "a" => arithmeticClosedTerminalScale data H j hj u hu
local notation "E" => arithmeticTerminalParameterEquiv data H 0 j hj u hu
local notation "B" => arithmeticRetainedClosingEquiv data H 0 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "F" => arithmeticTerminalNormalizationBoundary data H 0 j hj u hu
local notation "N" => independentScale τ (arithmeticClosedSmoothing_zero data H) (a true) (a false)
local notation "v₁" => fixedTerminalPolygonFirstBoundaryUnit data 0 j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "v₂" => fixedTerminalPolygonSecondBoundaryUnit data 0 j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "w" => arithmeticRetainedClosingUnit data H 0 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))

/-- The actual inverse Laurent substitution at order zero is the full original scalar correction. -/
theorem arithmeticTerminalNormalizationEquiv_closed (b : Bool) :
    (arithmeticTerminalNormalizationEquiv data H 0 j hj u hu b).toAlgHom =
      PolygonScaledReciprocal.scaling (a b) := by
  have hp : (E b).toAlgHom.comp (PolygonScaledReciprocal.scaling (a b)) = (B).toAlgHom := by
    have he : (E b).toAlgHom =
        LaurentUnitPoints.evalUnit (R := Q) (if b then v₁ else v₂) := by
      cases b <;> rfl
    rw [he, LaurentUnitPoints.evalUnit_scaling]
    exact congrArg (fun z : Q[T;T⁻¹]ˣ ↦ LaurentUnitPoints.evalUnit (R := Q) z)
      (arithmeticClosedTerminalScale_unit data H j hj u hu b)
  apply AlgHom.ext
  intro z
  apply (E b).injective
  exact ((E b).apply_symm_apply _).trans (DFunLike.congr_fun hp z).symm

/-- The closed correction gives exactly both prescribed full algebra boundaries. -/
theorem arithmeticTerminalNormalizationBoundary_closed (b : Bool) :
    (if b then leftLaurentMap τ else (leftLaurentMap τ).comp (branchSwapMap τ)).comp N =
      F b := by
  rw [arithmeticTerminalNormalizationBoundary, arithmeticTerminalNormalizationEquiv_closed]
  cases b
  · exact rightLaurentMap_independentScale τ (arithmeticClosedSmoothing_zero data H) _ _
  · exact leftLaurentMap_independentScale τ (arithmeticClosedSmoothing_zero data H) _ _

/-- Both full Laurent coordinate tests hold unconditionally in the actual order-zero quotient. -/
theorem arithmeticTerminalBoundaryCompatible_closed :
    ArithmeticTerminalBoundaryCompatible data H 0 j hj u hu := by
  have hl := arithmeticTerminalNormalizationBoundary_closed data H j hj u hu true
  have hr := arithmeticTerminalNormalizationBoundary_closed data H j hj u hu false
  constructor
  · rw [← DFunLike.congr_fun hl (leftCoordinate τ), ← DFunLike.congr_fun hr (leftCoordinate τ)]
    exact laurentCompatible_restrictions τ (N (leftCoordinate τ))
  · rw [← DFunLike.congr_fun hl (rightCoordinate τ),
      ← DFunLike.congr_fun hr (rightCoordinate τ)]
    exact laurentCompatible_restrictions τ (N (rightCoordinate τ))

/-- The constructed extension is the previous simultaneous closed map on the entire node ring. -/
theorem arithmeticTerminalBoundaryExtension_closed :
    arithmeticTerminalBoundaryExtension data H 0 j hj u hu
      (arithmeticTerminalBoundaryCompatible_closed data H j hj u hu) = N := by
  exact (arithmeticTerminalBoundaryExtension_unique data H 0 j hj u hu
    (arithmeticTerminalBoundaryCompatible_closed data H j hj u hu) N
    (arithmeticTerminalNormalizationBoundary_closed data H j hj u hu true)
    (arithmeticTerminalNormalizationBoundary_closed data H j hj u hu false)).symm

/-- Each candidate specializes to its actual independently scaled original coordinate. -/
theorem arithmeticTerminalCoordinateLift_closed (b : Bool) :
    arithmeticTerminalCoordinateLift data H 0 j hj u hu b =
      algebraMap Q (ChartRing τ) (a b) *
        (if b then leftCoordinate τ else rightCoordinate τ) := by
  cases b
  · rw [← arithmeticTerminalBoundaryExtension_right data H 0 j hj u hu
        (arithmeticTerminalBoundaryCompatible_closed data H j hj u hu),
      arithmeticTerminalBoundaryExtension_closed, independentScale_right]
    rfl
  · rw [← arithmeticTerminalBoundaryExtension_left data H 0 j hj u hu
        (arithmeticTerminalBoundaryCompatible_closed data H j hj u hu),
      arithmeticTerminalBoundaryExtension_closed, independentScale_left]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
