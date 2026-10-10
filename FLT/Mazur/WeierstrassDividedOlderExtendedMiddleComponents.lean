/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderExtendedOrigins
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The full middle-component cover over residue extensions

The conic and both ordered lines cover the actual older chart after extension.
The two complete rational parameter charts still cover the full conic, even
when the divided constant is zero. All maps are full scheme pullbacks.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "C" => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
local notation "L₁" => olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk
local notation "L₂" => olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk

/-- Extension retains the full conic and ordered-line decomposition of the original chart. -/
theorem olderExtendedMiddleComponents_cover :
    Set.range (pullback.fst p C) ∪
      (Set.range (pullback.fst p L₁) ∪ Set.range (pullback.fst p L₂)) =
      Set.range (pullback.fst p (olderGlobalTensorChart hπ data K j hj r hr)) := by
  simp only [Scheme.Pullback.range_fst, ← Set.preimage_union,
    olderGlobalMiddleComponents_cover]

/-- Both rational parameter charts cover the entire conic after extension. -/
theorem olderExtendedMiddleConicParameters_cover :
    Set.range (pullback.fst p
      (olderGlobalMiddleConicFirstParameter hπ data D j hj r hr hk0 hk)) ∪
    Set.range (pullback.fst p
      (olderGlobalMiddleConicSecondParameter hπ data D j hj r hr hk0 hk)) =
        Set.range (pullback.fst p C) := by
  simp only [Scheme.Pullback.range_fst, ← Set.preimage_union,
    olderGlobalMiddleConicParameters_cover]

end FLT.Mazur.WeierstrassDividedDepth
