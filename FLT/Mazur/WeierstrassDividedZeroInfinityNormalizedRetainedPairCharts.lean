/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedTerminalIntersection

/-!
# Whole retained charts in the double attachment

Explicit pushout inclusions retain both complete corrected original nodes.
Their comparison is the identity on these whole nodes, with the exact twists
confined to the initial attachment maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroDiagonalAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m
local notation "a" => fun b ↦ pushout.inl (w b) (r b)
local notation "t" => fun b ↦ pushout.inl (v b) (r b)
local notation "E" => arithmeticZeroInfinityNormalizedRetainedPairIso hπ data H m hj u hu
local notation "j" => arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H m hj u hu
local notation "A" => arithmeticZeroDiagonalAtlasObject hπ data H m hj u hu
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu

/-- Each entire original retained node is included in the full source double attachment. -/
def arithmeticZeroInfinityNormalizedRetainedPairSourceChart (b : Bool) :
    A (.retained ⟨0, by omega⟩ b) ⟶ pushout (a false) (a true) :=
  match b with
  | false => pushout.inr (w false) (r false) ≫ pushout.inl (a false) (a true)
  | true => pushout.inr (w true) (r true) ≫ pushout.inr (a false) (a true)

/-- The independent double attachment includes both entire original retained nodes. -/
def arithmeticZeroInfinityNormalizedRetainedPairTargetChart (b : Bool) :
    A (.retained ⟨0, by omega⟩ b) ⟶
      arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H m hj u hu :=
  match b with
  | false => pushout.inr (v false) (r false) ≫ pushout.inl (t false) (t true)
  | true => pushout.inr (v true) (r true) ≫ pushout.inr (t false) (t true)

local notation "s" => arithmeticZeroInfinityNormalizedRetainedPairSourceChart hπ data H m hj u hu
local notation "k" => arithmeticZeroInfinityNormalizedRetainedPairTargetChart hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedRetainedPairSourceChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (s b) := by
  cases b <;> unfold arithmeticZeroInfinityNormalizedRetainedPairSourceChart <;> infer_instance

instance arithmeticZeroInfinityNormalizedRetainedPairTargetChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (k b) := by
  cases b <;> unfold arithmeticZeroInfinityNormalizedRetainedPairTargetChart <;> infer_instance

/-- Both full retained inclusions keep the exact original global chart. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairSourceChart_global (b : Bool) :
    s b ≫ j = c (.retained ⟨0, by omega⟩ b) := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedRetainedPairSourceChart, Category.assoc,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_opposite,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_retained]

/-- The five-chart comparison acts identically on both complete retained nodes. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairSourceChart_comparison (b : Bool) :
    s b ≫ (E).hom = k b := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedRetainedPairSourceChart,
      arithmeticZeroInfinityNormalizedRetainedPairTargetChart, Category.assoc,
      arithmeticZeroInfinityNormalizedRetainedPairIso_first,
      arithmeticZeroInfinityNormalizedRetainedPairIso_opposite,
      arithmeticZeroInfinityNormalizedRetainedPushoutIso_retained_assoc]

end FLT.Mazur.WeierstrassDividedDepth
