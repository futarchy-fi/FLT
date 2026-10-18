/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialRetainedReflection
public import FLT.Mazur.WeierstrassDividedVariableRetainedIntersection

/-!
# Full retained intersections in the independent revised target

The exact cyclic classification is expressed using the named target charts,
so original normalization maps can use it without expanding the target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "c" => arithmeticRevisedPolygonRetainedChart data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
attribute [local irreducible] arithmeticRevisedPolygon
  PolygonVariableSmoothing.scheme PolygonVariableSmoothing.chartWithParameter

/-- All full target retained intersections preserve their original arm and outgoing puncture. -/
theorem arithmeticRevisedRetained_intersection (idx other : Fin (j + 1)) (b e : Bool)
    (x y : PolygonSmoothing.chart Q τ)
    (h : c idx b ((O b).hom x) = c other e ((O e).hom y)) :
    (idx = other ∧ b = e) ∨
      (idx.val + 1 = other.val ∧ b = e ∧ x ∈ Set.range (leftBranchOpen Q τ)) ∨
      (other.val + 1 = idx.val ∧ b = e ∧ y ∈ Set.range (leftBranchOpen Q τ)) := by
  apply variableRetained_intersection Q (j + 1) τ p
    (fun idx b ↦ (arithmeticRevisedPolygonParameter_retained data H m j hj u hu idx b).symm)
    idx other b e x y
  simp only [twistedRetainedOrientation, revisedOrientation_hom] at h
  convert h using 1
  unfold arithmeticRevisedPolygon arithmeticRevisedPolygonRetainedChart
  rfl

end FLT.Mazur.WeierstrassDividedDepth
