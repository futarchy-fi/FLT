/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentBoundary
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer
public import FLT.Mazur.SchemeOpenChartRange

/-!
# The full adjacent boundary target is horizontally punctured

Recover the original next retained coordinates from the indexed target.
Every point in the actual boundary range has nonzero horizontal coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  PrincipalOpenTensor.transitionIso TensorProduct
/-- A known factorization carries every point of the first map's range to the composite range. -/
theorem fixedBoundary_mem_range_of_factorization {X Y Z : Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (he : f ≫ g = h)
    (p : Y) (hp : p ∈ Set.range f) : g p ∈ Set.range h := by
  obtain ⟨q, rfl⟩ := hp
  exact ⟨q, (congrArg (fun m => m q) he).symm⟩

/-- A composite range is contained in the range of its final map. -/
theorem fixedBoundary_mem_range_right {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : Z) (hp : p ∈ Set.range (f ≫ g)) : p ∈ Set.range g := by
  obtain ⟨q, rfl⟩ := hp
  exact ⟨f q, rfl⟩

variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (j : ℕ) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, by omega⟩
local notation "eNext" => data ⟨j + 2, by omega⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) 2
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso Q x u (previousBoundaryEquiv hπ e eNext)
local notation "a" => (A).inv ≫ PrincipalOpenTensor.inclusion Q t
local notation "b" => (B).inv ≫ PrincipalOpenTensor.inclusion Q u
local notation "ia" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "ib" => (Fin.succ ⟨k - (j + 1), by omega⟩ : Fin (k + 3))
local notation "leftIso" => arithmeticRetainedTensorIso hπ data m k hk j (by omega)
local notation "rightIso" => arithmeticRetainedTensorIso hπ data m k hk (j + 1) (by omega)
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk

/-- Recover next retained coordinates with the domain declared as the global indexed chart. -/
def arithmeticFixedAdjacentTargetCoordinates :
    globalTensorAtlasObject hπ data Q k hk ib ⟶
      Spec (.of (ScalarExtension W (π ^ (start + (j + 1))) π
        (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q)) := (rightIso).inv

attribute [local irreducible] arithmeticFixedAdjacentTargetCoordinates
  arithmeticFixedAdjacentBoundaryTarget
local notation "coords" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

/-- Undoing the target indexing recovers the original principal boundary map. -/
@[reassoc] theorem arithmeticFixedAdjacentBoundaryTarget_inverse :
    arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj ≫ coords = b := by
  unfold arithmeticFixedAdjacentBoundaryTarget arithmeticFixedAdjacentTargetCoordinates
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option maxHeartbeats 800000 in
-- Compare the original tensor coordinate instances at the recovered boundary point.
/-- Every full target-boundary point has nonzero uncontracted horizontal coordinate. -/
theorem arithmeticFixedAdjacentBoundaryTarget_punctured
    (p : globalTensorAtlasObject hπ data Q k hk ib)
    (hp : p ∈ Set.range (arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj)) :
    tu ∉ (coords p).asIdeal := by
  have hp' := fixedBoundary_mem_range_of_factorization
    (arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj) coords b
    (arithmeticFixedAdjacentBoundaryTarget_inverse hπ data m k hk j hj) p hp
  apply (PrincipalOpenTensor.mem_inclusion_range Q u _).mp
  exact fixedBoundary_mem_range_right _ _ _ hp'

end FLT.Mazur.WeierstrassDividedDepth
