/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodePushout
public import FLT.Mazur.WeierstrassDividedOlderZeroIndexedNodeCover
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSections

/-!
# Localized equalizer charts on the original retained start-zero atlas

The two ordered principal node opens refine the exact original atlas object.
They retain their whole images and the original global marked sections.
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
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "Obj" => globalTensorAtlasObject hπ data K (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))
local notation "G" => globalTensorAtlasMap hπ data K (j + 1 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))

/-- The ordered equalizer source, with the original tangent sign on each open. -/
def olderZeroIndexedEqualizerObject (i : Fin 2) : Scheme :=
  Fin.cases (Spec (.of (FullNodeEqualizer a c ha)))
    (fun _ => Spec (.of (FullNodeEqualizer (-a) c (ha).neg))) i

/-- Each matching-pair spectrum is the full original localized node chart. -/
def olderZeroIndexedEqualizerIso (i : Fin 2) :
    olderZeroIndexedEqualizerObject data D j hj i ≅ olderZeroIndexedNodeObject data j hj i := by
  cases i using Fin.cases with
  | zero => exact fullNodeEqualizerIso a c ha
  | succ i => exact fullNodeEqualizerIso (-a) c (ha).neg

/-- The equalizer charts map to the precise retained atlas object. -/
def olderZeroIndexedEqualizerMap (i : Fin 2) :
    olderZeroIndexedEqualizerObject data D j hj i ⟶ Obj :=
  (olderZeroIndexedEqualizerIso data D j hj i).hom ≫
    olderZeroIndexedNodeMap hπ data D j hj r hr hk0 hk i

instance olderZeroIndexedEqualizerMap_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk i) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

omit [IsBezout R] in
/-- No part of either original node open is discarded by the comparison. -/
theorem olderZeroIndexedEqualizerMap_range (i : Fin 2) :
    Set.range (olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk i) =
      Set.range (olderZeroIndexedNodeMap hπ data D j hj r hr hk0 hk i) :=
  (olderZeroIndexedEqualizerIso data D j hj i).hom.homeomorph.surjective.range_comp _

omit [IsBezout R] in
/-- Every point of the retained first atlas chart lies in one of these equalizers. -/
theorem olderZeroIndexedEqualizerMap_cover (z : Obj) :
    ∃ i x, olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk i x = z := by
  obtain ⟨i, x, hx⟩ := olderZeroIndexedNodeMap_cover hπ data D j hj r hr hk0 hk z
  have hz : z ∈ Set.range (olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk i) := by
    rw [olderZeroIndexedEqualizerMap_range]
    exact ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hz
  exact ⟨i, y, hy⟩

/-- The complete original retained first chart has a two-member equalizer open cover. -/
def olderZeroIndexedEqualizerOpenCover : (Obj).OpenCover where
  I₀ := Fin 2
  X := olderZeroIndexedEqualizerObject data D j hj
  f := olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨olderZeroIndexedEqualizerMap_cover hπ data D j hj r hr hk0 hk,
      olderZeroIndexedEqualizerMap_isOpenImmersion hπ data D j hj r hr hk0 hk⟩

/-- The first chart retains exactly the original global node inclusion. -/
@[reassoc] theorem olderZeroIndexedEqualizerMap_first_global :
    olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk 0 ≫ G =
      (fullNodeEqualizerIso a c ha).hom ≫
        olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk := by
  rw [olderZeroIndexedEqualizerMap, Category.assoc, olderZeroIndexedNodeMap_first_global]
  rfl

/-- The second chart retains its opposite ordered global inclusion. -/
@[reassoc] theorem olderZeroIndexedEqualizerMap_second_global :
    olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk 1 ≫ G =
      (fullNodeEqualizerIso (-a) c (ha).neg).hom ≫
        olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk := by
  rw [olderZeroIndexedEqualizerMap, Category.assoc, olderZeroIndexedNodeMap_second_global]
  rfl

/-- The first localized branch origin is the original first global retained section. -/
@[reassoc] theorem olderZeroIndexedEqualizerMap_first_origin :
    NodeLocalDescent.firstOrigin K (fullNodeNormalizedDenominator a c)
        (fullNodeNormalizedDenominator_value a c ha) ≫
      NodeLocalDescent.firstBranch K (fullNodeNormalizedDenominator a c)
        (fullNodeNormalizedDenominator_value a c ha) ≫
      olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk 0 ≫ G =
        olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderZeroIndexedEqualizerMap_first_global]
  have H := fullNodeFirstBranch_origin_assoc a c ha
    (olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk)
  rw [olderGlobalZeroFirstNode_origin] at H
  simpa only [fullNodeFirstBranch, Category.assoc] using H

/-- The other signed chart origin is the original second global retained section. -/
@[reassoc] theorem olderZeroIndexedEqualizerMap_second_origin :
    NodeLocalDescent.firstOrigin K (fullNodeNormalizedDenominator (-a) c)
        (fullNodeNormalizedDenominator_value (-a) c (ha).neg) ≫
      NodeLocalDescent.firstBranch K (fullNodeNormalizedDenominator (-a) c)
        (fullNodeNormalizedDenominator_value (-a) c (ha).neg) ≫
      olderZeroIndexedEqualizerMap hπ data D j hj r hr hk0 hk 1 ≫ G =
        olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderZeroIndexedEqualizerMap_second_global]
  have H := fullNodeFirstBranch_origin_assoc (-a) c (ha).neg
    (olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk)
  rw [olderGlobalZeroSecondNode_origin] at H
  simpa only [fullNodeFirstBranch, Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
