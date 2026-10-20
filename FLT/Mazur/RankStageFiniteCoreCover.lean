/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteCoreCoverage

/-!
# Finite original principal covers of entire rank loci

Noetherian compactness applies to an arbitrary subset of the original rank
locus. Thus finitely many original principal domains cover all its points,
with one coherent invariant core for each domain. The cores may differ;
this theorem does not identify coefficients chosen on different cores.
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
local instance coreCoverOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coreCoverOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coreCoverOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- Every subset of an old rank domain has a finite cover by coherent original domains. -/
theorem exists_rankStage_original_finite_core_cover (n : ℕ) (W : A.Opens)
    (s : Set A) (hsW : s ⊆ W) (hsn : s ⊆ exactRank (Over.mk p) n) :
    ∃ C : Finset (Γ(A, ⊤) × Γ(A, ⊤)),
      (∀ c ∈ C, ∃ ha : A.basicOpen c.1 ≤ rankImageOpen (Over.mk p) n,
        A.basicOpen c.2 ≤ W ∧ A.basicOpen c.2 ≤ rankImageOpen (Over.mk p) n ∧
        ∀ k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.2 ≤
          rankStageCore e n c.1 ha k) ∧
      s ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A) := by
  classical
  let _ : IsNoetherianRing Γ(A, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top A⟩
  let _ : TopologicalSpace.NoetherianSpace A := noetherianSpace_of_isAffine
  let good : Set (Γ(A, ⊤) × Γ(A, ⊤)) := {c | ∃ ha :
    A.basicOpen c.1 ≤ rankImageOpen (Over.mk p) n,
    A.basicOpen c.2 ≤ W ∧ A.basicOpen c.2 ≤ rankImageOpen (Over.mk p) n ∧
    ∀ k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.2 ≤
      rankStageCore e n c.1 ha k}
  have hc : s ⊆ ⋃ c ∈ good, (A.basicOpen c.2 : Set A) := by
    intro x hx
    obtain ⟨a, ha, b, hb, hbU, hcore⟩ :=
      exists_rankStage_original_finite_neighborhood e n {x} (Set.finite_singleton x)
        (Set.singleton_subset_iff.mpr (hsn hx))
    obtain ⟨c, hc, hcb⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
      (A.basicOpen b ⊓ W) {x} (Set.finite_singleton x)
        (Set.singleton_subset_iff.mpr ⟨hb (Set.mem_singleton x), hsW hx⟩)
    refine Set.mem_iUnion₂.mpr ⟨(a, c), ⟨ha, hcb.trans inf_le_right,
      (hcb.trans inf_le_left).trans hbU, fun k ↦ ?_⟩, hc (Set.mem_singleton x)⟩
    exact ((TopologicalSpace.Opens.map (rankThickeningMap (Over.mk p) n k).base).monotone
      (hcb.trans inf_le_left)).trans (hcore k)
  obtain ⟨C, hC, hf, hcover⟩ :=
    (TopologicalSpace.NoetherianSpace.isCompact s).elim_finite_subcover_image
      (fun c (_ : c ∈ good) ↦ (A.basicOpen c.2).isOpen) hc
  exact ⟨hf.toFinset, fun c hc ↦ hC (hf.mem_toFinset.mp hc), by simpa using hcover⟩

omit [QuasiCompact p] [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p] in
/-- The selected domains cover every point at every infinitesimal order. -/
theorem rankStage_principal_cover_all_orders (n : ℕ)
    (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
    (hC : exactRank (Over.mk p) n ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A)) (k : ℕ) :
    (⨆ c ∈ C, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.2) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨c, hc, hy⟩ := Set.mem_iUnion₂.mp
    (hC ((rankThickeningMap_range (Over.mk p) n k).le ⟨y, rfl⟩))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c,
    TopologicalSpace.Opens.mem_iSup.mpr ⟨hc, hy⟩⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
