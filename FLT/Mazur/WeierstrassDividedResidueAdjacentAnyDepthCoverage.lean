/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueAdjacentPairCoverage
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensorIntersection
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer
public import FLT.Mazur.SchemeOpenChartRange

public import FLT.Mazur.WeierstrassSuccessiveXAnyDepthSmoothCover

/-!
# Actual adjacent pair coverage including zero creation depth

Smoothness is exactly membership in the horizontal puncture or the original
incidence transfer domain. A nonpunctured smooth input acquires punctured
coordinates without changing either actual input of its relative pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX IsLocalRing
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe v
variable {K : Type v} [Field K] (V : ValuationSubring K)
  {W : WeierstrassCurve V} {π : V} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "Q" => ResidueField V
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
local notation "old" => adjacentRetainedOldGlobalTensorChart hπ data Q j hj r hr
local notation "next" => olderGlobalTensorChart hπ data Q (j + 1) hjNext r hr
local notation "s" => pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap V Q)))
  (finiteGlobalStructure hπ data (j + 2 + r) hr)
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => adjacentRetainedGlobalTensor_isPullback hπ data Q j hj hjNext r hr
variable {Y : Scheme.{v}} (g : Y ⟶ Spec (.of (ResidueField V)))


local notation "O" => residueAdjacentPairOpen V hπ data j hj r hr g
local notation "transfer" => residueAdjacentPairTransfer V hπ data j hj hjNext r hr g
local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

include D in
/-- The two full original pair opens test precisely smoothness at every creation depth. -/
theorem residueAdjacentPairOpen_anyDepth_smooth_iff
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme)) :
    old (pullback.fst f g p) ∈ (s).smoothLocus ↔
      oldU ∉ (pullback.fst f g p).asIdeal ∨ p ∈ O := by
  rw [residueAdjacentPairOpen_mem]
  exact (residueAnyDepth_mem_smooth_iff D (start + j) hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) old s
    (adjacentZeroAbscissa_chart_structure V hπ data j hj r hr) _).trans or_comm

include D in
/-- Zero abscissa forces the actual boundary condition, also for zero-depth inputs. -/
theorem residueAdjacentPairOpen_anyDepth_zero_mem
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) : p ∈ O := by
  have h := (residueAdjacentPairOpen_anyDepth_smooth_iff V hπ data D j hj r hr g hk p).mp hs
  exact h.resolve_left (not_not.mpr hz)

include D in
/-- The transferred point is an actual relative pair with the same two ambient inputs. -/
theorem residueAdjacentPair_anyDepth_zero_coordinates
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) :
    ∃ q : (pullback f' g : Scheme),
      next (pullback.fst f' g q) = old (pullback.fst f g p) ∧
      pullback.snd f' g q = pullback.snd f g p ∧
      tu ∉ (pullback.fst f' g q).asIdeal := by
  let v : (O).toScheme :=
    ⟨p, residueAdjacentPairOpen_anyDepth_zero_mem V hπ data D j hj r hr g hk p hs hz⟩
  refine ⟨transfer v, ?_, ?_, residueAdjacentPairTransfer_punctured V hπ data j hj hjNext r hr g v⟩
  · exact congrArg (fun k => k v) (residueAdjacentPairTransfer_first V hπ data j hj hjNext r hr g)
  · exact congrArg (fun k => k v) (residueAdjacentPairTransfer_second V hπ data j hj hjNext r hr g)

end FLT.Mazur.WeierstrassDividedDepth
