/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialRetainedReflection
public import FLT.Mazur.WeierstrassDividedRetainedChartOpen
public import FLT.Mazur.WeierstrassDividedRetainedPuncturePreimage
public import FLT.Mazur.WeierstrassDividedRevisedRetainedTargetIntersection
public import FLT.Mazur.WeierstrassDividedRetainedTransport

/-!
# Reflection of all original retained intersections

The full normalization is sealed before transporting point classifications.
Its nonfinal nodes preserve the entire outgoing puncture.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticRetainedFixedSmoothingIso
/-- Reflect a point using a morphism equation and an exact full preimage. -/
theorem revisedMap_preimage_mem {X Y : Scheme} (f g : X ⟶ Y) (hf : f = g)
    (U : Set Y) (V : Set X) (hg : g ⁻¹' U = V) (x : X) (hx : f x ∈ U) : x ∈ V := by
  rw [← hg]
  change g x ∈ U
  rw [← hf]
  exact hx

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 1 H.scale_div)
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "C" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
local notation "l" => leftBranchOpen Q (parameter R π 1)
local notation "r" => precedingBranch Q (parameter R π 1)

local notation "p" => arithmeticRevisedPolygonParameter data H 1 j hj u hu
local notation "K" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu


omit [IsBezout R] in
/-- The complete normalization before orientation, including the last-node correction. -/
irreducible_def arithmeticFirstRevisedRetainedNodeMap (idx : Fin (j + 1)) (b : Bool) :
    PolygonSmoothing.chart Q (parameter R π 1) ⟶ PolygonSmoothing.chart Q τ :=
  (C idx).hom ≫ (if idx.val = j then K b else Iso.refl _).hom

local notation "N" => arithmeticFirstRevisedRetainedNodeMap hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H 1
local notation "c" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu

omit [IsBezout R] in
/-- The original retained map factors through its sealed full normalization. -/
theorem arithmeticFirstRevisedRetainedNodeMap_chart (idx : Fin (j + 1)) (b : Bool) :
    G (.retained idx b) = N idx b ≫ (O b).hom ≫ c idx b := by
  rw [arithmeticFirstRevisedRetainedNodeMap_def, Category.assoc]
  exact arithmeticFirstRevisedRetained_normalized hπ data H j hj u hu idx b

omit [IsBezout R] in
/-- Before the closing depth, no residual correction is applied. -/
theorem arithmeticFirstRevisedRetainedNodeMap_nonfinal (idx : Fin (j + 1)) (b : Bool)
    (hne : idx.val ≠ j) : N idx b = (C idx).hom := by
  rw [arithmeticFirstRevisedRetainedNodeMap_def, ite_eq_right hne]
  exact Category.comp_id _

omit [IsBezout R] in
/-- Before the last node, the normalization reflects the whole outgoing puncture. -/
theorem arithmeticFirstRevisedRetainedNodeMap_left (idx : Fin (j + 1)) (b : Bool)
    (hi : idx.val + 1 < j + 1) (x : PolygonSmoothing.chart Q (parameter R π 1))
    (hx : N idx b x ∈ Set.range (leftBranchOpen Q τ)) : x ∈ Set.range l :=
  revisedMap_preimage_mem (N idx b) (C idx).hom
    (arithmeticFirstRevisedRetainedNodeMap_nonfinal hπ data H j hj u hu idx b
      (Nat.ne_of_lt (Nat.lt_of_succ_lt_succ hi))) _ _
    (arithmeticRetainedFixedSmoothingIso_left_preimage data H 1 (j + 1) hj idx) x hx

end FLT.Mazur.WeierstrassDividedDepth
