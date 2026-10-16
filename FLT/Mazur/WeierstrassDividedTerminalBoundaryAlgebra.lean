/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalEdgeCorrection
public import FLT.Mazur.PolygonSmoothingBoundaryLiftGeometry

/-!
# Actual Laurent algebra data for simultaneous terminal extension

Invert each full original terminal substitution after the retained substitution.
These give the required two restrictions of a terminal-chart correction, while
leaving the source overlaps unchanged. No coefficient reduction is performed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticRetainedClosingEquiv data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "T" => fixedTerminalPolygonBoundaryParameter data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu

/-- Select the full original Laurent substitution at the corresponding terminal branch. -/
def arithmeticTerminalParameterEquiv (b : Bool) : L ≃ₐ[Q] L :=
  if b then fixedTerminalFirstBoundaryEquiv data m j hj H.a1_unit (H.scale j)
    H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
  else fixedTerminalSecondBoundaryEquiv data m j hj H.a1_unit (H.scale j)
    H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)

local notation "E" => arithmeticTerminalParameterEquiv data H m j hj u hu

/-- Its spectrum is exactly the unchanged original terminal parameter map. -/
theorem arithmeticTerminalParameterEquiv_spec (b : Bool) :
    Spec.map (CommRingCat.ofHom (E b).toAlgHom.toRingHom) = T b := by
  cases b <;> rfl

/-- The branch substitution needed after the terminal chart, with all Laurent corrections. -/
def arithmeticTerminalNormalizationEquiv (b : Bool) : L ≃ₐ[Q] L :=
  (B).trans (E b).symm

/-- The required full node-to-Laurent map for either unchanged terminal puncture. -/
def arithmeticTerminalNormalizationBoundary (b : Bool) : ChartRing τ →ₐ[Q] L :=
  (arithmeticTerminalNormalizationEquiv data H m j hj u hu b).toAlgHom.comp
    (if b then leftLaurentMap τ else (leftLaurentMap τ).comp (branchSwapMap τ))

local notation "F" => arithmeticTerminalNormalizationBoundary data H m j hj u hu

/-- Compose with the actual original terminal parameter to recover the retained substitution. -/
theorem arithmeticTerminalNormalizationBoundary_parameter (b : Bool) :
    (E b).toAlgHom.comp (F b) = (B).toAlgHom.comp
      (if b then leftLaurentMap τ else (leftLaurentMap τ).comp (branchSwapMap τ)) := by
  apply AlgHom.ext
  intro z
  exact (E b).apply_symm_apply _

/-- The prescribed Laurent map gives the required square with each original source boundary. -/
@[reassoc] theorem arithmeticTerminalNormalizationBoundary_square (b : Bool) :
    T b ≫ Spec.map (CommRingCat.ofHom (F b).toRingHom) =
      Spec.map (CommRingCat.ofHom (B).toAlgHom.toRingHom) ≫
        (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) := by
  rw [← arithmeticTerminalParameterEquiv_spec data H m j hj u hu b]
  have hp : (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) =
      Spec.map (CommRingCat.ofHom
        (if b then leftLaurentMap τ else
          (leftLaurentMap τ).comp (branchSwapMap τ)).toRingHom) := by
    cases b
    · exact rightBranchOpen_eq_spec τ
    · exact leftBranchOpen_eq_spec Q τ
  rw [hp, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom
    (arithmeticTerminalNormalizationBoundary_parameter data H m j hj u hu b)))

end FLT.Mazur.WeierstrassDividedDepth
