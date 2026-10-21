/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueAdjacentPairCoverage
public import FLT.Mazur.WeierstrassDividedTensorIntegralRelativeSmooth

/-!
# Adjacent residue coverage from full indexed smooth inputs

A point of any indexed full smooth chart representing the original first
input supplies exactly the relative smoothness needed by the original
adjacent zero-abscissa coverage theorem.
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
variable {K : Type v} [Field K] (V : ValuationSubring K) [IsNoetherianRing V]
  {W : WeierstrassCurve V} {π : V} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "Q" => ResidueField V
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "old" => adjacentRetainedOldGlobalTensorChart hπ data Q j hj r hr
local notation "s" => pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap V Q)))
  (finiteGlobalStructure hπ data (j + 2 + r) hr)
local notation "f" => old ≫ s
variable {Y : Scheme.{v}} (g : Y ⟶ Spec (.of (ResidueField V)))

local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
variable (i : Fin (j + 2 + r + 3))
  (p : (pullback
    (adjacentRetainedOldGlobalTensorChart hπ data (ResidueField V) j hj r hr ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap V (ResidueField V))))
        (finiteGlobalStructure hπ data (j + 2 + r) hr)) g : Scheme))
  (z : globalTensorAtlasObject hπ data (ResidueField V) (j + 2 + r) hr i)
  (hz : globalTensorAtlasMap hπ data (ResidueField V) (j + 2 + r) hr i z =
    adjacentRetainedOldGlobalTensorChart hπ data (ResidueField V) j hj r hr
      (pullback.fst
        (adjacentRetainedOldGlobalTensorChart hπ data (ResidueField V) j hj r hr ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap V (ResidueField V))))
            (finiteGlobalStructure hπ data (j + 2 + r) hr)) g p))
  (hs : z ∈ tensorIntegralAtlasSmoothOpen hπ data (ResidueField V) (j + 2 + r) hr i)

include hz hs in
/-- The exact indexed smooth condition gives relative smoothness of the original input. -/
theorem residueAdjacentIndexedSource_smooth :
    old (pullback.fst f g p) ∈ (s).smoothLocus := by
  have ht := (tensorIntegralAtlasSmoothOpen_mem_relative hπ data Q
    (j + 2 + r) hr i z).mp hs
  rwa [hz] at ht

include D hz hs in
/-- A zero-abscissa input represented in the full smooth atlas lies in its actual boundary. -/
theorem residueAdjacentPairOpen_zero_mem_of_indexedSmooth
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (hu : u ∈ (pullback.fst f g p).asIdeal) :
    p ∈ residueAdjacentPairOpen V hπ data j hj r hr g :=
  residueAdjacentPairOpen_zero_mem V hπ data D j hj r hr g hk0 hk p
    (residueAdjacentIndexedSource_smooth V hπ data j hj r hr g i p z hz hs) hu

include D hz hs in
/-- The puncture and original adjacent pair domain cover every such indexed smooth input. -/
theorem residueAdjacentPairOpen_cover_of_indexedSmooth
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth) :
    u ∉ (pullback.fst f g p).asIdeal ∨ p ∈ residueAdjacentPairOpen V hπ data j hj r hr g :=
  residueAdjacentPairOpen_smooth_cover V hπ data D j hj r hr g hk0 hk p
    (residueAdjacentIndexedSource_smooth V hπ data j hj r hr g i p z hz hs)

end FLT.Mazur.WeierstrassDividedDepth
