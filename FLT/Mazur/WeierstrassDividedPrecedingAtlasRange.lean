/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalExterior

/-!
# All earlier atlas charts lie in the full preceding exterior

The original finite atlas factors through one retention at every later stage.
The same containment holds for the complete tensor and global chart maps.
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
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)

/-- Every earlier exterior index factors through the original preceding exterior. -/
theorem precedingExteriorAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (finiteExteriorAtlasMap hπ data E₀ (j + 1 + r) hr
      ⟨i.val + 1 + r, by omega⟩) ⊆
        Set.range ((E).retained hπ e ≫ finiteStageRetained hπ data (j + 1) hj r hr) := by
  induction r with
  | zero =>
    rintro _ ⟨a, rfl⟩
    exact ⟨finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i a, rfl⟩
  | succ r ih =>
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := ih (Nat.le_of_succ_le hr) ⟨a, rfl⟩
    refine ⟨b, ?_⟩
    change ((finiteExterior hπ data E₀ (j + 1 + r) (Nat.le_of_succ_le hr)).retained
      hπ _) (((E).retained hπ e ≫
        finiteStageRetained hπ data (j + 1) hj r (Nat.le_of_succ_le hr)) b) = _
    rw [hb]
    rfl

/-- The corresponding full finite atlas indices lie in the original preceding open. -/
theorem precedingFiniteAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (finiteAtlasMap hπ data E₀ (j + 1 + r) hr
      ⟨i.val + 1 + r + 1, by omega⟩) ⊆
        Set.range (olderPrecedingExterior hπ data j hj r hr) := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := precedingExteriorAtlas_range_subset hπ data j hj r hr i ⟨a, rfl⟩
  exact ⟨b, congrArg (Exterior.exteriorChart
    (finiteExterior hπ data E₀ (j + 1 + r) hr)) hb⟩

variable (S : Type u) [CommRing S] [Algebra R S]
local notation "base" => finiteStructure hπ data (j + 1 + r) hr
local notation "old" => olderPrecedingExterior hπ data j hj r hr
local notation "p" => pullback.snd
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) base

/-- Base change retains the full preceding-exterior containment for every earlier chart. -/
theorem precedingTensorAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (finiteTensorAtlasMap hπ data S (j + 1 + r) hr
      ⟨i.val + 1 + r + 1, by omega⟩) ⊆
        Set.range (TensorOpenExterior.inclusion S base old) := by
  rintro _ ⟨a, rfl⟩
  rw [TensorOpenExterior.inclusion_range]
  apply precedingFiniteAtlas_range_subset hπ data j hj r hr i
  have H := finiteTensorAtlasMap_isPullback hπ data S (j + 1 + r) hr
    ⟨i.val + 1 + r + 1, by omega⟩
  exact ⟨_, (congrArg (fun f => f a) H.w).symm⟩

variable [IsBezout R]

/-- Each earlier original global atlas object is contained in the whole preceding exterior. -/
theorem precedingGlobalTensorAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (globalTensorAtlasMap hπ data S (j + 1 + r) hr
      (Fin.succ ⟨i.val + 1 + r + 1, by omega⟩)) ⊆
        Set.range (olderGlobalExteriorTensorChart hπ data S j hj r hr) := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := precedingTensorAtlas_range_subset hπ data j hj r hr S i ⟨a, rfl⟩
  exact ⟨b, congrArg (finiteLocalTensorEmbedding hπ data S (j + 1 + r) hr) hb⟩

end FLT.Mazur.WeierstrassDividedDepth
