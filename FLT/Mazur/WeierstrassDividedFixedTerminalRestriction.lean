/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFixedTerminalParameterIso
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalEvaluationRestriction
public import FLT.Mazur.PolygonSmoothingBranchSwapNaturality

/-!
# Fixed terminal parameters and their inverses follow restriction

The original Laurent coefficient map commutes with the actual normalized
boundary parameters. This follows from the full-node squares and cancellation
of the standard puncture inclusions, not from discarding nilpotent terms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] arithmeticTerminalSmoothing arithmeticFixedTerminalUnit
  fixedTerminalPolygonIso terminalArithmeticNodeEvaluation fixedTerminalPolygonBoundaryParameter
variable (R : Type) [CommRing R] (π : R) (m : ℕ)
local notation "F" => Spec.map (CommRingCat.ofHom
  (PolygonScalingNaturality.coeffMap (AlgHom.toRingHom (restriction R π m))))
variable {W : WeierstrassCurve R} (ha : IsUnit W.a₁)
local notation "τ" => fun a ↦ arithmeticInitialMobiusSmoothing W ha (π ^ 1) π a
local notation "P" => Spec.map (CommRingCat.ofHom
  (ringMap (AlgHom.toRingHom (restriction R π m))
    (τ (m + 1)) (τ m) (arithmeticInitialMobiusSmoothing_restriction W ha (π ^ 1) π m)))
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)

/-- Either normalized terminal branch preserves the original Laurent coefficient map. -/
@[reassoc] theorem fixedTerminalPolygonBranch_restriction (opposite : Bool) :
    (if opposite then leftBranchOpen Q₀ (τ m)
      else rightBranchOpen Q₀ (τ m)) ≫ P =
    F ≫ (if opposite then leftBranchOpen Q₁ (τ (m + 1))
      else rightBranchOpen Q₁ (τ (m + 1))) := by
  cases opposite
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← leftBranchOpen_branchSwapIso Q₀ (τ m), Category.assoc,
      branchSwapIso_ringMap, ← Category.assoc, leftBranchOpen_ringMap,
      Category.assoc, leftBranchOpen_branchSwapIso]
  · exact leftBranchOpen_ringMap (restriction R π m).toRingHom
      (τ (m + 1)) (τ m) (arithmeticInitialMobiusSmoothing_restriction W ha (π ^ 1) π m)

variable [IsDomain R] (hπ : π ≠ 0)
  {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
  (u : Rˣ) (hprimitive : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
include hπ
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "T" => fun a ↦ fixedTerminalPolygonBoundaryParameter data a j hj
  ha hs h2 h3 h4 h6 u hprimitive
local notation "E" => fun a b ↦ Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (terminalArithmeticNodeEvaluation data a j hj ha hs h2 h3 h4 h6 b)))
local notation "I" => fun a ↦ fixedTerminalPolygonIso π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive a

/-- The exact original-to-polygon Laurent parameter changes commute with quotient restriction. -/
@[reassoc] theorem fixedTerminalPolygonBoundaryParameter_restriction (opposite : Bool) :
    F ≫ T (m + 1) opposite = T m opposite ≫ F := by
  let b₁ := if opposite then leftBranchOpen Q₁ (τ (m + 1))
    else rightBranchOpen Q₁ (τ (m + 1))
  let _ : IsOpenImmersion b₁ := by cases opposite <;> dsimp [b₁] <;> infer_instance
  apply (cancel_mono b₁).mp
  calc
    (F ≫ T (m + 1) opposite) ≫ b₁ = F ≫ E (m + 1) opposite ≫ (I (m + 1)).hom := by
      rw [Category.assoc]
      exact congrArg (F ≫ ·)
        (fixedTerminalPolygon_boundary data (m + 1) j hj
          ha hs h2 h3 h4 h6 u hprimitive opposite).symm
    _ = E m opposite ≫ (I m).hom ≫ P := by
      have he := terminalArithmeticNodeEvaluation_restriction_square
        data m j hj ha hs h2 h3 h4 h6 opposite
      have hi := fixedTerminalPolygonIso_restriction π W s
        (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive hπ m
      have he' := congrArg (· ≫ (I (m + 1)).hom) he
      simpa only [Category.assoc, hi] using he'
    _ = (T m opposite ≫ F) ≫ b₁ := by
      rw [← Category.assoc, fixedTerminalPolygon_boundary, Category.assoc,
        fixedTerminalPolygonBranch_restriction, Category.assoc]

/-- The constructed full inverse preserves the original quotient arrows as well. -/
@[reassoc] theorem fixedTerminalPolygonBoundaryParameter_inv_restriction (opposite : Bool) :
    F ≫ inv (T (m + 1) opposite) = inv (T m opposite) ≫ F := by
  apply (cancel_mono (T (m + 1) opposite)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Category.assoc, fixedTerminalPolygonBoundaryParameter_restriction R π m ha hπ,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
