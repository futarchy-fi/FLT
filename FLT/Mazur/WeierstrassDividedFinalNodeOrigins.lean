/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodesDistinct

/-!
# The indexed node family retains all original neighborhood origins

The equalities use the original ordered node charts and only the established
stage transport. Both full-node orientations at zero depth remain explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
  (j : Fin (s + 1))
local notation "K" => ResidueField R
local notation "r" => s + 1 - (j.val + 1)
local notation "hj" => (by omega : j.val + 1 ≤ n)
local notation "hr" => (by omega : j.val + 1 + r ≤ n)
local notation "hjDepth" => (by omega : 2 * (start + j.val + 1) ≤ depth)
local notation "c" => residue R (Data.b6 (data (Fin.mk (j.val + 1) (by omega))))
local notation "T" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K hr hs (by omega))
local notation "N₁" =>
  finalNodeSection hπ data D s hs hk hp (Sum.inl (Sum.inr (Prod.mk j 0)))
local notation "N₂" =>
  finalNodeSection hπ data D s hs hk hp (Sum.inl (Sum.inr (Prod.mk j 1)))

/-- The first positive-depth node origin is exactly the fixed first ordered member. -/
@[reassoc] theorem finalNodeSection_positive_first_origin (h : 0 < start + j.val) :
    Spec.map (CommRingCat.ofHom (WeierstrassSuccessiveX.middleNodeOrigin c).toRingHom) ≫
      olderGlobalResidueFirstNode hπ data D j.val hj r hr h hjDepth ≫ T = N₁ := by
  rw [olderGlobalFirstNode_origin_assoc]
  change _ = orderedRetainedSection hπ data D j.val hj r hr hjDepth 0 ≫ T
  rw [orderedRetainedSection_positive hπ data D j.val hj r hr hjDepth h]
  rfl

/-- The opposite positive-depth origin is exactly the fixed second ordered member. -/
@[reassoc] theorem finalNodeSection_positive_second_origin (h : 0 < start + j.val) :
    Spec.map (CommRingCat.ofHom (WeierstrassSuccessiveX.middleNodeOrigin c).toRingHom) ≫
      olderGlobalResidueSecondNode hπ data D j.val hj r hr h hjDepth ≫ T = N₂ := by
  rw [olderGlobalSecondNode_origin_assoc]
  change _ = orderedRetainedSection hπ data D j.val hj r hr hjDepth 1 ≫ T
  rw [orderedRetainedSection_positive hπ data D j.val hj r hr hjDepth h]
  rfl

local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)

/-- The original scale-one first full-node origin survives the same stage transport. -/
@[reassoc] theorem finalNodeSection_zero_first_origin (h : start + j.val = 0) :
    Spec.map (CommRingCat.ofHom
      (WeierstrassModificationX.fullNodeOrigin a c ha).toRingHom) ≫
      olderGlobalZeroFirstNode hπ data D j.val hj r hr h hjDepth ≫ T = N₁ := by
  rw [olderGlobalZeroFirstNode_origin_assoc]
  change _ = orderedRetainedSection hπ data D j.val hj r hr hjDepth 0 ≫ T
  rw [orderedRetainedSection_zero hπ data D j.val hj r hr hjDepth h]
  rfl

/-- The signed scale-one second full-node origin keeps its original orientation. -/
@[reassoc] theorem finalNodeSection_zero_second_origin (h : start + j.val = 0) :
    Spec.map (CommRingCat.ofHom
      (WeierstrassModificationX.fullNodeOrigin (-a) c (ha).neg).toRingHom) ≫
      olderGlobalZeroSecondNode hπ data D j.val hj r hr h hjDepth ≫ T = N₂ := by
  rw [olderGlobalZeroSecondNode_origin_assoc]
  change _ = orderedRetainedSection hπ data D j.val hj r hr hjDepth 1 ≫ T
  rw [orderedRetainedSection_zero hπ data D j.val hj r hr hjDepth h]
  rfl

local notation "c₀" => residue R (Data.b6 (data (Fin.mk 0 (Nat.zero_lt_succ n))))

/-- The original first initial full-node origin is the initial member of the family. -/
@[reassoc] theorem finalNodeSection_initial_first_origin (hstart : 0 < start) :
    Spec.map (CommRingCat.ofHom
      (WeierstrassModificationX.fullNodeOrigin a c₀
        (WeierstrassModificationX.residue_tangent_isUnit D)).toRingHom) ≫
      initialGlobalResidueFirstNode hπ data D (s + 1) hs hstart (by omega) =
        finalNodeSection hπ data D s hs hk hp (.inl (.inl ⟨0, hstart⟩)) :=
  initialGlobalFirstNode_origin hπ data D (s + 1) hs hstart (by omega)

/-- The original oppositely oriented initial origin is the second initial member. -/
@[reassoc] theorem finalNodeSection_initial_second_origin (hstart : 0 < start) :
    Spec.map (CommRingCat.ofHom
      (WeierstrassModificationX.fullNodeOrigin (-a) c₀
        (WeierstrassModificationX.residue_tangent_isUnit D).neg).toRingHom) ≫
      initialGlobalResidueSecondNode hπ data D (s + 1) hs hstart (by omega) =
        finalNodeSection hπ data D s hs hk hp (.inl (.inl ⟨1, hstart⟩)) :=
  initialGlobalSecondNode_origin hπ data D (s + 1) hs hstart (by omega)

end FLT.Mazur.WeierstrassDividedDepth
