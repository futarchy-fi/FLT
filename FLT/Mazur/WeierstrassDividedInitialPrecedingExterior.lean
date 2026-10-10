/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalSectionExterior
public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart

/-!
# The original initial chart lies in every preceding exterior

The actual finite retention maps factor through intermediate stages. Their
coefficient pullbacks preserve this factorization as a full image inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

omit [IsBezout R] in
/-- Initial retention factors through any chosen intermediate retention stage. -/
theorem finiteRetained_stage_factor (k : ℕ) (hk : k ≤ n)
    (r : ℕ) (hr : k + r ≤ n) :
    finiteRetained hπ data E₀ (k + r) hr =
      finiteRetained hπ data E₀ k hk ≫ finiteStageRetained hπ data k hk r hr := by
  induction r with
  | zero => exact (Category.comp_id _).symm
  | succ r ih =>
    change (finiteRetained hπ data E₀ (k + r) (by omega) ≫ _) =
      finiteRetained hπ data E₀ k hk ≫ (finiteStageRetained hπ data k hk r (by omega) ≫ _)
    rw [ih, Category.assoc]
    rfl

omit [IsBezout R] in
/-- The complete initial chart factors through the original exterior preceding any step. -/
@[reassoc] theorem finiteInitialChart_preceding_factor (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) :
    finiteRetained hπ data E₀ j (by omega) ≫ olderPrecedingExterior hπ data j hj r hr =
      finiteInitialChart hπ data (j + 1 + r) hr := by
  rw [finiteInitialChart, finiteRetained_stage_factor hπ data (j + 1) hj r hr]
  change _ ≫ (_ ≫ _ ≫ _) = (_ ≫ _ ≫ _) ≫ _
  simp only [Category.assoc]

variable (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "f" => finiteStructure hπ data (j + 1 + r) hr
local notation "p" => pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) f
local notation "e" => olderPrecedingExterior hπ data j hj r hr

omit [IsBezout R] in
/-- The entire initial tensor chart lies in the coefficient pullback of each preceding exterior. -/
theorem finiteInitialTensorChart_preceding_range :
    Set.range (finiteInitialTensorChart hπ data S (j + 1 + r) hr) ⊆
      Set.range (TensorOpenExterior.inclusion S f e) := by
  rw [finiteInitialTensorChart_range, TensorOpenExterior.inclusion_range]
  intro z hz
  obtain ⟨a, ha⟩ := hz
  refine ⟨finiteRetained hπ data E₀ j (by omega) a, ?_⟩
  exact (congrArg (fun m => m a)
    (finiteInitialChart_preceding_factor hπ data j hj r hr)).trans ha

/-- The actual global initial tensor chart remains in each full preceding global exterior. -/
theorem globalInitialTensorChart_preceding_range :
    Set.range (globalInitialTensorChart hπ data S (j + 1 + r) hr) ⊆
      Set.range (olderGlobalExteriorTensorChart hπ data S j hj r hr) := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := finiteInitialTensorChart_preceding_range hπ data S j hj r hr ⟨a, rfl⟩
  exact ⟨b, congrArg (finiteLocalTensorEmbedding hπ data S (j + 1 + r) hr) hb⟩

omit j hj r hr in
/-- The complete initial tensor chart occupies the original final global atlas index. -/
theorem globalInitialTensorChart_range_index (t : ℕ) (ht : t ≤ n) :
    Set.range (globalInitialTensorChart hπ data S t ht) =
      Set.range (globalTensorAtlasMap hπ data S t ht ⟨t + 2, Nat.lt_succ_self _⟩) := by
  rw [← globalInitialTensorChart_eq_index hπ data S t ht]
  exact (finiteInitialTensorAtlasIso hπ data S t ht).hom.homeomorph.surjective.range_comp
    (globalTensorAtlasMap hπ data S t ht (Fin.succ ⟨t + 1, Nat.lt_succ_self _⟩))

end FLT.Mazur.WeierstrassDividedDepth
