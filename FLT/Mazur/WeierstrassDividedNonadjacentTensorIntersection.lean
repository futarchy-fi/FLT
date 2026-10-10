/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSkippedAtlasRange

/-!
# Empty non-adjacent intersections in the actual finite tensor atlas

Every indexed chart lying at least two positions beyond a retained successive
chart misses it when π vanishes. This includes all earlier successive charts
and the retained initial exterior, after every further modification.
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
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "F" => Exterior.advance hπ (E) e
local notation "tail" => finiteStageRetained hπ data (j + 2) hjNext r hr ≫
  Exterior.exteriorChart (finiteExterior hπ data E₀ (j + 2 + r) hr)
local notation "base" => finiteStructure hπ data (j + 2 + r) hr
local notation "new" => olderSuccessiveChart hπ data (j + 1) hjNext r hr

local notation "p" => pullback.snd
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) base
local notation "older" => skippedExteriorChart hπ data j hj hjNext r hr

/-- Every earlier indexed tensor chart lies in the full base-changed skipped exterior. -/
theorem nonadjacentTensorAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (finiteTensorAtlasMap hπ data S (j + 2 + r) hr
      ⟨i.val + 2 + r + 1, by omega⟩) ⊆
        Set.range (skippedExteriorTensorChart hπ data S j hj hjNext r hr) := by
  rintro _ ⟨a, rfl⟩
  have H := finiteTensorAtlasMap_isPullback hπ data S (j + 2 + r) hr
    ⟨i.val + 2 + r + 1, by omega⟩
  obtain ⟨b, hb⟩ := skippedFiniteAtlas_range_subset hπ data j hj hjNext r hr i
    (show p (finiteTensorAtlasMap hπ data S (j + 2 + r) hr
      ⟨i.val + 2 + r + 1, by omega⟩ a) ∈ Set.range
        (finiteAtlasMap hπ data E₀ (j + 2 + r) hr ⟨i.val + 2 + r + 1, by omega⟩) from
      ⟨_, (congrArg (fun f => f a) H.w).symm⟩)
  obtain ⟨c, _, hc⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback older p) b _ hb
  exact ⟨c, hc⟩

include hj hjNext

/-- All non-adjacent original tensor charts are disjoint at their actual finite indices. -/
theorem nonadjacentTensorAtlas_disjoint (i : Fin (j + 1)) (hp : algebraMap R S π = 0) :
    Disjoint (Set.range (finiteTensorAtlasMap hπ data S (j + 2 + r) hr
      ⟨i.val + 2 + r + 1, by omega⟩))
      (Set.range (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩)) := by
  have H := (skippedExteriorTensor_disjoint hπ data S j hj hjNext r hr hp).mono_left
    (nonadjacentTensorAtlas_range_subset hπ data S j hj hjNext r hr i)
  have he := olderSuccessiveTensorAtlasIso_map hπ data S (j + 1) hjNext r hr
  rw [← he] at H
  have hrange := (olderSuccessiveTensorAtlasIso hπ data S (j + 1) hjNext r hr).hom
    |>.homeomorph.surjective.range_comp
      (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩)
  exact H.mono_right (by rw [← hrange]; exact Set.Subset.rfl)

/-- Their entire scheme-theoretic intersection is empty. -/
theorem nonadjacentTensorAtlas_isPullback (i : Fin (j + 1))
    (hp : algebraMap R S π = 0) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨i.val + 2 + r + 1, by omega⟩)
      (finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩) := by
  let oldMap := finiteTensorAtlasMap hπ data S (j + 2 + r) hr
    ⟨i.val + 2 + r + 1, by omega⟩
  let newMap := finiteTensorAtlasMap hπ data S (j + 2 + r) hr ⟨r + 1, by omega⟩
  let _ := Scheme.isEmpty_pullback oldMap newMap
    (nonadjacentTensorAtlas_disjoint hπ data S j hj hjNext r hr i hp)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback oldMap newMap)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth
