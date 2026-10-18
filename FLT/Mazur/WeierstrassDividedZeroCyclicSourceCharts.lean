/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSeed
public import FLT.Mazur.PolygonSmoothingBranchSwapGeometry

/-!
# The five entire cyclic seed nodes in the original stage

The initial nodes enter through the full initial/infinity union. Reflecting
both true-branch nodes puts every source puncture in the cyclic orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroDiagonalAtlasChart
  arithmeticZeroInfinityNormalizedFullComparison
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

/-- The unreflected entire initial node enters the original full open union. -/
def arithmeticZeroCyclicInitialChart (b : Bool) : PolygonSmoothing.chart Q τ ⟶ X :=
  (if b then pushout.inr r r' else pushout.inl r r') ≫ (F).inv ≫ (U).ι

local notation "a" => arithmeticZeroCyclicInitialChart hπ data H m hj u hu

instance arithmeticZeroCyclicInitialChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (a b) := by
  cases b <;> unfold arithmeticZeroCyclicInitialChart <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The whole seed nodes, with both true-branch coordinate swaps, in the actual source. -/
def arithmeticZeroCyclicSourceChart (i : ZeroCyclicVertex) :
    PolygonSmoothing.chart Q ((S).parameter m i) ⟶ X :=
  match i with
  | .terminal => c .terminal
  | .retained false => c (.retained ⟨0, by omega⟩ false)
  | .retained true =>
      (branchSwapIso Q ((D).last m true)).hom ≫ c (.retained ⟨0, by omega⟩ true)
  | .initial false => a false
  | .initial true => (branchSwapIso Q τ).hom ≫ a true

instance arithmeticZeroCyclicSourceChart_isOpenImmersion (i : ZeroCyclicVertex) :
    IsOpenImmersion (arithmeticZeroCyclicSourceChart hπ data H m hj u hu i) := by
  rcases i with _ | (_ | _) | (_ | _) <;>
    dsimp only [arithmeticZeroCyclicSourceChart] <;> infer_instance

/-- Each entire unreflected initial left puncture is the full original retained attachment. -/
@[reassoc] theorem arithmeticZeroCyclicInitialChart_left (b : Bool) :
    leftBranchOpen Q τ ≫ a b =
      arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu b ≫ (U).ι := by
  unfold arithmeticZeroCyclicInitialChart
  rw [← Category.assoc]
  change arithmeticZeroInfinityNormalizedTargetLeft data H m b ≫ _ = _
  rw [← arithmeticZeroInfinityNormalizedRetainedToUnion_comparison hπ data H m hj u hu b]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The two full initial nodes meet along the original common infinity edge. -/
@[reassoc] theorem arithmeticZeroCyclicInitialChart_common :
    r ≫ a false = (edgeInversion Q).hom ≫ r ≫ a true := by
  simp only [arithmeticZeroCyclicInitialChart, Bool.false_eq_true, ↓reduceIte]
  have h : r ≫ pushout.inl r r' = r' ≫ pushout.inr r r' := pushout.condition
  simpa only [Category.assoc] using congrArg (· ≫ (F).inv ≫ (U).ι) h

end FLT.Mazur.WeierstrassDividedDepth
