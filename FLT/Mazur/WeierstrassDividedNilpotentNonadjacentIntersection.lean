/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNonadjacentGlobalIntersection
public import FLT.Mazur.TensorOpenChartNilpotentSeparation

/-!
# Full nonadjacent intersections over nilpotent coefficient extensions

The original skipped-chart parameter exclusion separates every nonadjacent
indexed chart at all arithmetic orders, without killing the parameter itself.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n) (hp : IsNilpotent (algebraMap R S π))

include hp in
/-- Nilpotence separates the entire earlier exterior from the next retained tensor chart. -/
theorem skippedExteriorTensor_nilpotent_disjoint :
    Disjoint (Set.range (skippedExteriorTensorChart hπ data S j hj hjNext r hr))
      (Set.range (olderSuccessiveTensorChart hπ data (j + 1) hjNext r hr S)) :=
  TensorOpenChart.nilpotent_disjoint (finiteStructure hπ data (j + 2 + r) hr)
    (skippedExteriorChart hπ data j hj hjNext r hr)
    (olderSuccessiveChart hπ data (j + 1) hjNext r hr)
    (olderSuccessiveChart_structure hπ data (j + 1) hjNext r hr) π hp
    (skippedExterior_parameter_notMem hπ data j hj hjNext r hr)

include hj hjNext hp in
/-- Every pair of nonadjacent original indexed tensor charts remains disjoint. -/
theorem nonadjacentTensorAtlas_nilpotent_disjoint (i : Fin (j + 1)) :
    Disjoint (Set.range (finiteTensorAtlasMap hπ data S (j + 2 + r) hr
      ⟨i.val + 2 + r + 1, by omega⟩))
      (Set.range (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩)) := by
  have H := (skippedExteriorTensor_nilpotent_disjoint hπ data S j hj hjNext r hr hp).mono_left
    (nonadjacentTensorAtlas_range_subset hπ data S j hj hjNext r hr i)
  rw [← olderSuccessiveTensorAtlasIso_map hπ data S (j + 1) hjNext r hr] at H
  have hrange := (olderSuccessiveTensorAtlasIso hπ data S (j + 1) hjNext r hr).hom
    |>.homeomorph.surjective.range_comp
      (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩)
  exact H.mono_right (by rw [← hrange]; exact Set.Subset.rfl)

include hj hjNext hp in
/-- The complete nonadjacent tensor intersection is the empty scheme over a nilpotent base. -/
theorem nonadjacentTensorAtlas_nilpotent_isPullback (i : Fin (j + 1)) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨i.val + 2 + r + 1, by omega⟩)
      (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩) := by
  let oldMap := finiteTensorAtlasMap hπ data S (j + 2 + r) hr
    ⟨i.val + 2 + r + 1, by omega⟩
  let newMap := finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩
  let _ := Scheme.isEmpty_pullback oldMap newMap
    (nonadjacentTensorAtlas_nilpotent_disjoint hπ data S j hj hjNext r hr hp i)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback oldMap newMap)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

variable [IsBezout R] (i : Fin (j + 1))
local notation "old" => globalTensorAtlasMap hπ data S (j + 2 + r) hr
  (Fin.succ (Fin.mk (i.val + 2 + r + 1) (by omega)))
local notation "new" => globalTensorAtlasMap hπ data S (j + 2 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))

include hj hjNext hp in
/-- Globalization retains the entire empty intersection at every nilpotent coefficient order. -/
theorem nonadjacentGlobalTensorAtlas_nilpotent_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) old new := by
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (finiteLocalTensorEmbedding hπ data S (j + 2 + r) hr)
    (nonadjacentTensorAtlas_nilpotent_isPullback hπ data S j hj hjNext r hr hp i).cone
    (nonadjacentTensorAtlas_nilpotent_isPullback hπ data S j hj hjNext r hr hp i).isLimit)

include hj hjNext hp in
/-- The actual nonadjacent global tensor charts have disjoint images over the full thickening. -/
theorem nonadjacentGlobalTensorAtlas_nilpotent_disjoint :
    Disjoint (Set.range old) (Set.range new) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (nonadjacentGlobalTensorAtlas_nilpotent_isPullback hπ data S j hj hjNext r hr hp i)
    a b hb.symm
  exact isEmptyElim z

end FLT.Mazur.WeierstrassDividedDepth
