/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentPairTransfer
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticSmoothCover
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Full arithmetic adjacent coverage at every creation depth

Smoothness forces each nonpunctured first input into its actual incidence
transfer domain. The second input is arbitrary and its whole morphism is retained.
The maximal-ideal generator and numeric node-depth conditions remain explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
  (hgen : IsLocalRing.maximalIdeal R = ideal R π)
  (m j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "eNext" => data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩
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
local notation "old" => finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr
local notation "next" => finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 2 + r) hr m
local instance arithmeticAdjacentCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local instance arithmeticAdjacentCoverage_open : IsOpenImmersion old := by
  let _ : IsOpenImmersion (adjacentRetainedOldChart hπ data j hj r hr) := by
    unfold adjacentRetainedOldChart
    infer_instance
  unfold finiteArithmeticAdjacentOldTensorChart adjacentRetainedOldGlobalTensorChart
    adjacentRetainedOldTensorChart
  infer_instance

local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => adjacentArithmeticTensor_isPullback hπ data m j hj hjNext r hr
variable {Y : Scheme}
  (g : Y ⟶ Spec (.of (PolygonArithmeticStages.Quotient R π m)))

local notation "O" => arithmeticAdjacentPairOpen hπ data m j hj r hr g
local notation "transfer" => arithmeticAdjacentPairTransfer hπ data m j hj hjNext r hr g
local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

include D hgen in
/-- Both original opens cover exactly the smooth arithmetic first input, at any depth. -/
theorem arithmeticAdjacentPairOpen_anyDepth_smooth_iff
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme)) :
    old (pullback.fst f g p) ∈ (s).smoothLocus ↔
      oldU ∉ (pullback.fst f g p).asIdeal ∨ p ∈ O := by
  rw [arithmeticAdjacentPairOpen_mem]
  exact (arithmeticAnyDepth_chart_mem_smooth_iff D hπ hgen (start + j) hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) m old s
    (finiteArithmeticAdjacentOldTensorChart_structure hπ data m j hj r hr) _).trans or_comm

include D hgen in
/-- A smooth arithmetic input with zero horizontal coordinate lies in the actual boundary. -/
theorem arithmeticAdjacentPairOpen_anyDepth_zero_mem
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) : p ∈ O := by
  have he := (arithmeticAdjacentPairOpen_anyDepth_smooth_iff
    hπ data D hgen m j hj r hr g hk p).mp hs
  exact he.resolve_left (not_not.mpr hz)

include D hgen in
/-- The actual arithmetic pair acquires a punctured first input without changing either input. -/
theorem arithmeticAdjacentPair_anyDepth_zero_coordinates
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) :
    ∃ q : (pullback f' g : Scheme),
      next (pullback.fst f' g q) = old (pullback.fst f g p) ∧
      pullback.snd f' g q = pullback.snd f g p ∧
      tu ∉ (pullback.fst f' g q).asIdeal := by
  let v : (O).toScheme :=
    ⟨p, arithmeticAdjacentPairOpen_anyDepth_zero_mem hπ data D hgen m j hj r hr g hk p hs hz⟩
  refine ⟨transfer v, ?_, ?_,
    arithmeticAdjacentPairTransfer_punctured hπ data m j hj hjNext r hr g v⟩
  · exact congrArg (fun k => k v)
      (arithmeticAdjacentPairTransfer_first hπ data m j hj hjNext r hr g)
  · exact congrArg (fun k => k v)
      (arithmeticAdjacentPairTransfer_second hπ data m j hj hjNext r hr g)

end FLT.Mazur.WeierstrassDividedDepth
