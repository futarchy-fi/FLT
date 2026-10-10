/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentZeroNormalizedIntersection
public import FLT.Mazur.WeierstrassSuccessiveXZeroIncidenceBoundary
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSections

/-!
# Initial ordered nodes cannot enter the next successive chart

The full adjacent pullback and the original vanishing boundary coordinates
exclude both node sections from the entire next chart at every later stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom copen)))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "A" => PrincipalOpenTensor.transitionIso K x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso K x uNext
  (previousBoundaryEquiv hπ e fData)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext r hr
local notation "E" => zeroResidueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

local notation "pFirst" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (zeroFirstIncidenceMap D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))))
local notation "pSecond" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (zeroSecondIncidenceMap D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))))

/-- The original first ordered node with only its common target-stage index reassociated. -/
def adjacentZeroFirstSection := pFirst ≫ g

/-- The actual first node remains outside the entire next chart at every retained stage. -/
theorem adjacentZeroFirstSection_next_disjoint :
    Disjoint (Set.range (adjacentZeroFirstSection hπ data D j hj hk0 hk r hr))
      (Set.range gNext) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
    (adjacentZeroNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr)
    (pFirst a) b hb.symm
  obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (zeroFirstIncidenceBoundary_isPullback D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))
    ((E).hom v) a hv
  exact isEmptyElim w

/-- The complete first-node and next-chart fiber product is empty. -/
theorem adjacentZeroFirstSection_next_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (adjacentZeroFirstSection hπ data D j hj hk0 hk r hr) gNext := by
  let _ := Scheme.isEmpty_pullback _ _
    (adjacentZeroFirstSection_next_disjoint hπ data D j hj hk0 hk hjNext r hr)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback _ _)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Reassociation changes no original first section or point. -/
theorem adjacentZeroFirstSection_original :
    HEq (olderGlobalZeroFirstSection hπ data D j hj (r + 1) (by omega) hk0 hk)
      (adjacentZeroFirstSection hπ data D j hj hk0 hk r hr) := by
  unfold olderGlobalZeroFirstSection olderGlobalZeroSuccessiveChart adjacentZeroFirstSection
  rw [← Category.assoc]
  change HEq ((Spec.map _ ≫ Spec.map _) ≫ _) (_ ≫ _)
  rw [← Spec.map_comp]
  exact heq_comp rfl rfl
    (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr (by omega)) HEq.rfl
    (adjacentRetainedOldGlobalTensorChart_heq hπ data K j hj r hr)

/-- The original second ordered node with only its common target-stage index reassociated. -/
def adjacentZeroSecondSection := pSecond ≫ g

/-- The actual second node remains outside the entire next chart at every retained stage. -/
theorem adjacentZeroSecondSection_next_disjoint :
    Disjoint (Set.range (adjacentZeroSecondSection hπ data D j hj hk0 hk r hr))
      (Set.range gNext) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
    (adjacentZeroNormalized_isPullback hπ data D j hj hk0 hk hjNext r hr)
    (pSecond a) b hb.symm
  obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (zeroSecondIncidenceBoundary_isPullback D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))
    ((E).hom v) a hv
  exact isEmptyElim w

/-- The complete second-node and next-chart fiber product is empty. -/
theorem adjacentZeroSecondSection_next_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (adjacentZeroSecondSection hπ data D j hj hk0 hk r hr) gNext := by
  let _ := Scheme.isEmpty_pullback _ _
    (adjacentZeroSecondSection_next_disjoint hπ data D j hj hk0 hk hjNext r hr)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback _ _)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- Reassociation changes no original second section or point. -/
theorem adjacentZeroSecondSection_original :
    HEq (olderGlobalZeroSecondSection hπ data D j hj (r + 1) (by omega) hk0 hk)
      (adjacentZeroSecondSection hπ data D j hj hk0 hk r hr) := by
  unfold olderGlobalZeroSecondSection olderGlobalZeroSuccessiveChart adjacentZeroSecondSection
  rw [← Category.assoc]
  change HEq ((Spec.map _ ≫ Spec.map _) ≫ _) (_ ≫ _)
  rw [← Spec.map_comp]
  exact heq_comp rfl rfl
    (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr (by omega)) HEq.rfl
    (adjacentRetainedOldGlobalTensorChart_heq hπ data K j hj r hr)

end FLT.Mazur.WeierstrassDividedDepth
