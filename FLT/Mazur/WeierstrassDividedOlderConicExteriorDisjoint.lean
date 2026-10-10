/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderGlobalExterior
public import FLT.Mazur.WeierstrassSuccessiveXResidueBoundaryDisjoint

/-!
# A retained conic never acquires an intersection with its preceding exterior

The original conic kills the preceding horizontal coordinate. Its entire
intersection with the preceding exterior is therefore empty at every later
retained stage, including the actual global embeddings.
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
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
open WeierstrassModificationX
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "C" => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
local notation "X" => olderGlobalExteriorTensorChart hπ data K j hj r hr

/-- The preceding exterior and retained conic have the empty scheme as their full intersection. -/
theorem olderGlobalConicExterior_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) X C := by
  have H := residueConicHorizontal_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
  convert! H.paste_horiz
    (olderGlobalExteriorTensor_isPullback hπ data K j hj r hr) using 1
  exact Scheme.empty_ext _ _

/-- Later modifications introduce no point shared by this conic and its preceding exterior. -/
theorem olderGlobalConicExterior_disjoint : Disjoint (Set.range X) (Set.range C) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let E := (olderGlobalConicExterior_isPullback hπ data D j hj r hr hk0 hk).isoPullback
  exact E.symm.hom.homeomorph.isEmpty

/-- The full exterior-conic intersection comparison is the empty scheme. -/
def olderGlobalConicExteriorPullbackIso : (∅ : Scheme.{u}) ≅ pullback X C :=
  (olderGlobalConicExterior_isPullback hπ data D j hj r hr hk0 hk).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
