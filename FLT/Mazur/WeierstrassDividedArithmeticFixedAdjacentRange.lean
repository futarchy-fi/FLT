/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentSource
public import FLT.Mazur.WeierstrassSuccessiveXTensorBoundaryRange

/-!
# Exact coordinate tests for indexed adjacent arithmetic boundaries

The source is precisely the original incidence open and the target is precisely
the next horizontal puncture. Both descriptions hold at every quotient order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
open scoped TensorProduct
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  PrincipalOpenTensor.transitionIso TensorProduct
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
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

attribute [local irreducible] arithmeticFixedAdjacentSourceCoordinates
  arithmeticFixedAdjacentBoundarySource arithmeticFixedAdjacentBoundaryTarget
  arithmeticFixedAdjacentTargetCoordinates
local notation "sourceCoords" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "targetCoords" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

local notation "src" => arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj
local notation "tgt" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj

omit [IsBezout R] in
/-- The full indexed source is exactly the original incidence nonvanishing domain. -/
theorem arithmeticFixedAdjacentBoundarySource_mem
    (p : globalTensorAtlasObject hπ data Q k hk ia) :
    p ∈ Set.range src ↔ tt ∉ (sourceCoords p).asIdeal := by
  rw [arithmeticBoundary_range_comp_iso src sourceCoords,
    arithmeticFixedAdjacentBoundarySource_inverse]
  have he := SchemeOpenChartRange.range_iso_comp (A).symm
    (PrincipalOpenTensor.inclusion Q t)
  have hb := tensorBoundary_mem_range W (π ^ (start + j)) π
    (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0 (sourceCoords p)
  exact (congrArg (fun U => sourceCoords p ∈ U) he).to_iff.trans hb

omit [IsBezout R] in
/-- The full indexed target is exactly the next original abscissa puncture. -/
theorem arithmeticFixedAdjacentBoundaryTarget_mem
    (p : globalTensorAtlasObject hπ data Q k hk ib) :
    p ∈ Set.range tgt ↔ tu ∉ (targetCoords p).asIdeal := by
  rw [arithmeticBoundary_range_comp_iso tgt targetCoords,
    arithmeticFixedAdjacentBoundaryTarget_inverse]
  have he := SchemeOpenChartRange.range_iso_comp (B).symm
    (PrincipalOpenTensor.inclusion Q u)
  have hb := tensorBoundary_mem_range W (π ^ (start + (j + 1))) π
    (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2 (targetCoords p)
  exact (congrArg (fun U => targetCoords p ∈ U) he).to_iff.trans hb

end FLT.Mazur.WeierstrassDividedDepth
