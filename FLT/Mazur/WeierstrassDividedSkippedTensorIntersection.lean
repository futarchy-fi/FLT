/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSkippedChartSupport
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor
public import FLT.Mazur.TensorOpenChartVanishingSeparation

/-!
# Special-fiber separation across a skipped finite chart

The entire exterior before an intervening chart is disjoint from the next
chart after coefficient extension killing π. Later retention preserves this
empty intersection in the actual finite model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "F" => Exterior.advance hπ (E) e
local notation "tail" => finiteStageRetained hπ data (j + 2) hjNext r hr ≫
  Exterior.exteriorChart (finiteExterior hπ data E₀ (j + 2 + r) hr)
local notation "base" => finiteStructure hπ data (j + 2 + r) hr
local notation "new" => olderSuccessiveChart hπ data (j + 1) hjNext r hr

/-- The whole earlier exterior, retained across an intervening chart and every later step. -/
def skippedExteriorChart : (E).carrier ⟶ finiteModification hπ data (j + 2 + r) hr :=
  (E).retained hπ e ≫ (F).retained hπ fData ≫ tail

/-- This is the original exterior open immersion through the full retention chain. -/
instance skippedExteriorChart_isOpenImmersion :
    IsOpenImmersion (skippedExteriorChart hπ data j hj hjNext r hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _ ≫ _))

/-- Any original skipped intersection lies away from the special fiber. -/
theorem skippedExterior_parameter_notMem (a : (E).carrier) (c : stepX fData)
    (h : skippedExteriorChart hπ data j hj hjNext r hr a = new c) :
    π ∉ (base (new c)).asIdeal := by
  apply Exterior.skipped_intersection_parameter_notMem hπ (E) e fData tail base _ a c h
  have H := adjacentRetainedOldChart_structure hπ data j hj r hr
  rw [adjacentRetainedOldChart_eq hπ data j hj hjNext r hr] at H
  simpa only [Category.assoc] using H

local notation "p" => Limits.pullback.snd
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) base

/-- The entire older exterior in the actual finite coefficient pullback. -/
def skippedExteriorTensorChart :=
  pullback.snd (skippedExteriorChart hπ data j hj hjNext r hr) p

/-- Killing π separates the whole earlier exterior from the new actual tensor chart. -/
theorem skippedExteriorTensor_disjoint (hp : algebraMap R S π = 0) :
    Disjoint (Set.range (skippedExteriorTensorChart hπ data S j hj hjNext r hr))
      (Set.range (olderSuccessiveTensorChart hπ data (j + 1) hjNext r hr S)) :=
  TensorOpenChart.vanishing_disjoint base
    (skippedExteriorChart hπ data j hj hjNext r hr) new
    (olderSuccessiveChart_structure hπ data (j + 1) hjNext r hr) π hp
    (skippedExterior_parameter_notMem hπ data j hj hjNext r hr)

/-- The full skipped special-fiber intersection is the empty scheme. -/
theorem skippedExteriorTensor_isPullback (hp : algebraMap R S π = 0) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (skippedExteriorTensorChart hπ data S j hj hjNext r hr)
      (olderSuccessiveTensorChart hπ data (j + 1) hjNext r hr S) :=
  TensorOpenChart.vanishing_isPullback base
    (skippedExteriorChart hπ data j hj hjNext r hr) new
    (olderSuccessiveChart_structure hπ data (j + 1) hjNext r hr) π hp
    (skippedExterior_parameter_notMem hπ data j hj hjNext r hr)

end FLT.Mazur.WeierstrassDividedDepth
