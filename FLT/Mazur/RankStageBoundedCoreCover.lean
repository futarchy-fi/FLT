/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteCoreCover

/-!
# Finitely many coherent core domains across all original ranks

The original Noetherian source has a uniform rank bound. At each rank,
compactness constructs finitely many coherent original principal domains.
Together they cover every original point, including the lower-rank residual
loci. Pulling back the coverage retains every point of an arbitrary test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance boundedCoverOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundedCoverOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundedCoverOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- Every original open is covered by finitely many domains at finitely many exact ranks. -/
theorem exists_rankStage_bounded_original_core_cover (W : A.Opens) :
    ∃ (N : ℕ) (C : Fin (N + 1) → Finset (Γ(A, ⊤) × Γ(A, ⊤))),
      (∀ n c, c ∈ C n → ∃ ha : A.basicOpen c.1 ≤ rankImageOpen (Over.mk p) n.val,
        A.basicOpen c.2 ≤ W ∧ A.basicOpen c.2 ≤ rankImageOpen (Over.mk p) n.val ∧
        ∀ k, rankThickeningMap (Over.mk p) n.val k ⁻¹ᵁ A.basicOpen c.2 ≤
          rankStageCore e n.val c.1 ha k) ∧
      ∀ x : A, x ∈ W → ∃ n : Fin (N + 1), x ∈ exactRank (Over.mk p) n.val ∧
        ∃ c ∈ C n, x ∈ A.basicOpen c.2 := by
  classical
  let _ : IsNoetherianRing Γ(A, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top A⟩
  let _ : TopologicalSpace.NoetherianSpace A := noetherianSpace_of_isAffine
  obtain ⟨N, hN⟩ := exists_finite_exactRank_cover (Over.mk p)
  obtain ⟨C, hC⟩ := Classical.axiomOfChoice fun n : Fin (N + 1) ↦
    exists_rankStage_original_finite_core_cover e n.val W
      ((W : Set A) ∩ exactRank (Over.mk p) n.val)
      Set.inter_subset_left Set.inter_subset_right
  refine ⟨N, C, fun n ↦ (hC n).1, fun x hx ↦ ?_⟩
  obtain ⟨n, hn, hxn⟩ := hN x
  let i : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  refine ⟨i, hxn, ?_⟩
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp ((hC i).2 ⟨hx, hxn⟩)
  exact ⟨c, hc, hxc⟩

/-- The same finite family covers entire original test images, without finite-fiber input. -/
theorem exists_rankStage_bounded_test_core_cover (W : A.Opens)
    {ι : Type} (T : ι → Type) (g : ∀ i, T i → A)
    (hg : ∀ i x, g i x ∈ W) :
    ∃ (N : ℕ) (C : Fin (N + 1) → Finset (Γ(A, ⊤) × Γ(A, ⊤))),
      (∀ n c, c ∈ C n → ∃ ha : A.basicOpen c.1 ≤ rankImageOpen (Over.mk p) n.val,
        A.basicOpen c.2 ≤ W ∧ A.basicOpen c.2 ≤ rankImageOpen (Over.mk p) n.val ∧
        ∀ k, rankThickeningMap (Over.mk p) n.val k ⁻¹ᵁ A.basicOpen c.2 ≤
          rankStageCore e n.val c.1 ha k) ∧
      ∀ i x, ∃ n : Fin (N + 1), g i x ∈ exactRank (Over.mk p) n.val ∧
        ∃ c ∈ C n, g i x ∈ A.basicOpen c.2 := by
  obtain ⟨N, C, hC, hcover⟩ := exists_rankStage_bounded_original_core_cover e W
  exact ⟨N, C, hC, fun i x ↦ hcover (g i x) (hg i x)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
