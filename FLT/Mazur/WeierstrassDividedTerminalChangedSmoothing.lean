/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalTangentRestriction
public import FLT.Mazur.WeierstrassDividedClosingTransportSpan
public import FLT.Mazur.PolygonSmoothingChangeParameter

/-!
# A changed terminal smoothing with exact residual closing gluing

The two actual tangent scales determine the new smoothing. The whole terminal
chart is rescaled once. Both residual Laurent transitions are retained in full;
no assertion that tangent agreement eliminates their higher coefficients is made.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "a" => arithmeticTerminalTangentScale data H m j hj u hu

/-- The changed smoothing absorbs the product of the two actual tangent weights. -/
def arithmeticTerminalChangedSmoothing : Q := (a true : Q) * a false * τ

local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu

/-- One full chart isomorphism realizes both tangent scales with the changed smoothing. -/
def arithmeticTerminalChangedIso : PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q σ :=
  changeParameterIso τ σ (a true) (a false) rfl

local notation "N" => arithmeticTerminalChangedIso data H m j hj u hu

/-- Both standard punctures commute with the same whole-node isomorphism. -/
@[reassoc] theorem arithmeticTerminalChangedIso_branch (b : Bool) :
    (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) ≫ (N).hom =
      (edgeScalingIso (a b)).hom ≫
        (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) := by
  cases b
  · exact rightBranch_changeParameter ..
  · exact leftBranch_changeParameter ..

/-- The full residual transition after changing the terminal smoothing. -/
def arithmeticTerminalResidualTwist (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  arithmeticClosingTerminalTwist data H m j hj u hu b ≪≫ edgeScalingIso (a b)

/-- The revised terminal gluing retains every coefficient of the original transitions. -/
def arithmeticTerminalChangedBoundary (b : Bool) :
    branchTorus Q ⟶ PolygonSmoothing.chart Q σ :=
  (arithmeticTerminalResidualTwist data H m j hj u hu b).hom ≫
    (if b then leftBranchOpen Q σ else rightBranchOpen Q σ)

instance arithmeticTerminalChangedBoundary_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticTerminalChangedBoundary data H m j hj u hu b) := by
  unfold arithmeticTerminalChangedBoundary
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- Replacing the terminal target preserves the exact full original transported boundary. -/
@[reassoc] theorem arithmeticTerminalChangedBoundary_transport (b : Bool) :
    arithmeticClosingTerminalBoundary data H m j hj u hu b ≫ (N).hom =
      arithmeticTerminalChangedBoundary data H m j hj u hu b := by
  simp only [arithmeticClosingTerminalBoundary, arithmeticTerminalChangedBoundary,
    arithmeticTerminalResidualTwist, Iso.trans_hom, Category.assoc]
  rw [arithmeticTerminalChangedIso_branch]

/-- The new terminal chart still lies over the original arithmetic coefficient spectrum. -/
@[reassoc] theorem arithmeticTerminalChangedIso_base :
    (N).hom ≫ chartStructure Q σ = chartStructure Q τ :=
  changeParameterIso_base ..

/-- The changed smoothing specializes to the original zero smoothing on the closed fiber. -/
theorem arithmeticTerminalChangedSmoothing_closed :
    arithmeticTerminalChangedSmoothing data H 0 j hj u hu = 0 := by
  unfold arithmeticTerminalChangedSmoothing
  rw [arithmeticClosedSmoothing_zero data H, mul_zero]

variable [IsDomain R] (hπ : π ≠ 0)
include hπ

/-- The explicitly changed coefficient follows the original quotient restriction. -/
theorem arithmeticTerminalChangedSmoothing_restriction :
    restriction R π m (arithmeticTerminalChangedSmoothing data H (m + 1) j hj u hu) = σ := by
  unfold arithmeticTerminalChangedSmoothing
  rw [map_mul, map_mul,
    arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m]
  have htrue := congrArg Units.val
    (arithmeticTerminalTangentScale_restriction data H j hj u hu hπ m true)
  have hfalse := congrArg Units.val
    (arithmeticTerminalTangentScale_restriction data H j hj u hu hπ m false)
  rw [show restriction R π m
      (arithmeticTerminalTangentScale data H (m + 1) j hj u hu true : Quotient R π (m + 1)) =
      (a true : Q) from htrue,
    show restriction R π m
      (arithmeticTerminalTangentScale data H (m + 1) j hj u hu false : Quotient R π (m + 1)) =
      (a false : Q) from hfalse]

end FLT.Mazur.WeierstrassDividedDepth
