/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoublePuncture
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentBranches

/-!
# Branch choices forced by both actual retained transfers

Each target lies on exactly one contracted branch. Classify the transferred
pair as positive, negative, or opposite without a caller-supplied branch.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticFixedAdjacentBoundarySource arithmeticFixedAdjacentBoundaryTarget
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (node : SplitNodeDepth W π depth) (m k : ℕ) (hk : k ≤ n)
  (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "a" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "b" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "x" => arithmeticFixedAdjacentBoundarySource hπ data m k hk i hi
local notation "z" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk i hi
local notation "y" => arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj
local notation "w" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj
local notation "hx" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk i hi
local notation "hy" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk j hj

local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj
local notation "t" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj

local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "ei" => data ⟨i + 2, by omega⟩
local notation "ej" => data ⟨j + 2, by omega⟩
local notation "u" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 2
local notation "v" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 2
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "vi" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q 1
local notation "vj" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q 1
local notation "Ti" => WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + (i + 1))) π
  (Data.b3 ei) (Data.b4 ei) (Data.b6 ei) Q
local notation "Tj" => WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + (j + 1))) π
  (Data.b3 ej) (Data.b4 ej) (Data.b6 ej) Q
local notation "αi" => algebraMap R Ti W.a₁
local notation "αj" => algebraMap R Tj W.a₁
local notation "pi" => fun p => I (pullback.fst (chart c ≫ s) (chart d ≫ s) (t p))
local notation "pj" => fun p => J (pullback.snd (chart c ≫ s) (chart d ≫ s) (t p))

include node in
/-- Every actual transferred pair belongs to one of the three addition branch regimes. -/
theorem arithmeticRetainedDoubleTransfer_branch_cases (p : (D).toScheme) :
    (u * vi ∈ (pi p).asIdeal ∧ v * vj ∈ (pj p).asIdeal) ∨
    (u * vi + αi * u ∈ (pi p).asIdeal ∧ v * vj + αj * v ∈ (pj p).asIdeal) ∨
    ((u * vi ∈ (pi p).asIdeal ∧ v * vj + αj * v ∈ (pj p).asIdeal) ∨
      (u * vi + αi * u ∈ (pi p).asIdeal ∧ v * vj ∈ (pj p).asIdeal)) := by
  have hp := arithmeticRetainedDoubleTransfer_ranges hπ data m k hk i j hi hj p
  have hi' := arithmeticFixedAdjacentBoundaryTarget_branches hπ data node m k hk i hi _ hp.1
  have hj' := arithmeticFixedAdjacentBoundaryTarget_branches hπ data node m k hk j hj _ hp.2
  rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
  · exact Or.inl ⟨hi', hj'⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hi', hj'⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hi', hj'⟩))
  · exact Or.inr (Or.inl ⟨hi', hj'⟩)

include node in
/-- Both branch choices are exclusive on the entire actual transfer domain. -/
theorem arithmeticRetainedDoubleTransfer_branches_exclusive (p : (D).toScheme) :
    ¬ (u * vi ∈ (pi p).asIdeal ∧ u * vi + αi * u ∈ (pi p).asIdeal) ∧
      ¬ (v * vj ∈ (pj p).asIdeal ∧ v * vj + αj * v ∈ (pj p).asIdeal) := by
  have hp := arithmeticRetainedDoubleTransfer_ranges hπ data m k hk i j hi hj p
  exact ⟨arithmeticFixedAdjacentBoundaryTarget_not_both hπ data node m k hk i hi _ hp.1,
    arithmeticFixedAdjacentBoundaryTarget_not_both hπ data node m k hk j hj _ hp.2⟩

end FLT.Mazur.WeierstrassDividedDepth
