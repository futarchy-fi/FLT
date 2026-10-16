/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedBoundaryUnits
public import FLT.Mazur.PolygonSmoothingIndependentScaling
public import FLT.Mazur.WeierstrassDividedFixedTerminalBoundary

/-!
# A simultaneous full terminal correction at arithmetic order zero

Both coefficients are constructed from the original units. Their independent
scalings extend over one whole terminal chart and match the same retained
closing parameter, with neither original source boundary changed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "L" => Q[T;T⁻¹]
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (H.a1_unit.map (algebraMap R Q))
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "v₁" => fixedTerminalPolygonFirstBoundaryUnit data 0 j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "v₂" => fixedTerminalPolygonSecondBoundaryUnit data 0 j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "w" => arithmeticRetainedClosingUnit data H 0 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "T" => fixedTerminalPolygonBoundaryParameter data 0 j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) w)))
local notation "puncture" => fun (b : Bool) ↦
  ite (b = true) (leftBranchOpen Q τ) (rightBranchOpen Q τ)

/-- Each coefficient corrects the corresponding actual terminal tangent to the retained power. -/
def arithmeticClosedTerminalScale (b : Bool) : Qˣ :=
  A ^ (2 * (j + 1)) /
    if b then arithmeticClosedTerminalFirstCoefficient data H j hj u hu else A

/-- Both complete Laurent units become the same retained unit after the constructed scaling. -/
theorem arithmeticClosedTerminalScale_unit (b : Bool) :
    Units.map (algebraMap Q L).toMonoidHom
      (arithmeticClosedTerminalScale data H j hj u hu b) * (if b then v₁ else v₂) = w := by
  rw [arithmeticClosedRetainedUnit_eq]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [arithmeticClosedTerminalSecondUnit_eq data H j hj]
    simp [arithmeticClosedTerminalScale, div_eq_mul_inv, mul_assoc]
  · simp only [↓reduceIte]
    rw [arithmeticClosedTerminalFirstUnit_eq data H j hj u hu]
    simp [arithmeticClosedTerminalScale, div_eq_mul_inv, mul_assoc]

/-- The full original parameter maps, not just their tangent values, are corrected. -/
@[reassoc] theorem arithmeticClosedTerminalScale_parameter (b : Bool) :
    T b ≫ (edgeScalingIso (arithmeticClosedTerminalScale data H j hj u hu b)).hom = B := by
  change Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
    (if b then v₁ else v₂)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling _).toRingHom) = _
  rw [LaurentUnitPoints.spec_evalUnit_scaling]
  exact congrArg (fun z : Lˣ ↦ Spec.map
    (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q) z).toRingHom))
      (arithmeticClosedTerminalScale_unit data H j hj u hu b)

/-- One constructed full-chart automorphism corrects both branches at once. -/
def arithmeticClosedTerminalNormalization :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  independentScalingIso τ (arithmeticClosedSmoothing_zero data H)
    (arithmeticClosedTerminalScale data H j hj u hu true)
    (arithmeticClosedTerminalScale data H j hj u hu false)

local notation "N" => arithmeticClosedTerminalNormalization data H j hj u hu

/-- Each restriction of that single automorphism has the independently constructed scale. -/
@[reassoc] theorem arithmeticClosedTerminalNormalization_boundary (b : Bool) :
    puncture b ≫ (N).hom =
      (edgeScalingIso (arithmeticClosedTerminalScale data H j hj u hu b)).hom ≫ puncture b := by
  cases b
  · exact rightBranch_independentScaling ..
  · exact leftBranch_independentScaling ..

/-- Both unchanged source boundaries now reach the retained parameter on the same target node. -/
@[reassoc] theorem arithmeticClosedTerminalNormalization_corrected (b : Bool) :
    T b ≫ puncture b ≫ (N).hom = B ≫ puncture b := by
  rw [arithmeticClosedTerminalNormalization_boundary, ← Category.assoc,
    arithmeticClosedTerminalScale_parameter]

end FLT.Mazur.WeierstrassDividedDepth
