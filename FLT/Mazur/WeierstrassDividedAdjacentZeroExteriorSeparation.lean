/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentZeroNormalizedIntersection
public import FLT.Mazur.WeierstrassSuccessiveXZeroExteriorBoundary
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroConic

/-!
# The full initial exterior line excludes the next retained chart

The original adjacent pullback globalizes the vanishing incidence coordinate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "L" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (zeroExteriorLineMap D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))))
local notation "E" => zeroResidueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The whole initial incidence line, with its target stage reassociated. -/
def adjacentZeroExteriorLine := L ≫ g

/-- The entire exterior line misses the next original retained chart. -/
theorem adjacentZeroExteriorLine_next_disjoint (hjNext : j + 2 ≤ n) :
    Disjoint (Set.range (adjacentZeroExteriorLine hπ data D j hj hk0 hk r hr))
      (Set.range (olderGlobalTensorChart hπ data K (j + 1) hjNext r hr)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
    (adjacentZeroNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr)
    (L a) b (ha.trans hb.symm)
  obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (zeroExteriorLineBoundary_isPullback D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))
    ((E).hom v) a hv
  exact isEmptyElim w

/-- Reassociation preserves the original full incidence line as a dependent map. -/
theorem adjacentZeroExteriorLine_original :
    HEq (olderGlobalZeroIncidence hπ data D j hj (r + 1) (by omega) hk0 hk)
      (adjacentZeroExteriorLine hπ data D j hj hk0 hk r hr) := by
  unfold olderGlobalZeroIncidence olderGlobalZeroSuccessiveChart adjacentZeroExteriorLine
  rw [← Category.assoc, ← zeroExteriorLineMap_spec]
  exact heq_comp rfl rfl
    (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr (by omega)) HEq.rfl
    (adjacentRetainedOldGlobalTensorChart_heq hπ data K j hj r hr)

end FLT.Mazur.WeierstrassDividedDepth
