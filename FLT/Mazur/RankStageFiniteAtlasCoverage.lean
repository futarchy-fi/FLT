/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteCoreCoverage
public import FLT.Mazur.SchemeFiniteTargetFiber

/-!
# Common-core neighborhoods for every member of a finite original atlas

Finite sets in the old chart domains are treated simultaneously. Each new
principal neighborhood stays inside its prescribed old domain, and every
order of every neighborhood lies in the same constructed invariant core.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples FiniteRelationAffinePrincipalCore
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteAtlasOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteAtlasOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteAtlasOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance finiteAtlasFirst_finite (n k : ℕ) : IsFinite (rankStageFirst (p := p) n k) :=
  rankStageFirst_finite n k

/-- One common core and compatible principal domains cover all prescribed finite chart sets. -/
theorem exists_rankStage_original_finite_atlas (n : ℕ)
    {ι : Type} [Finite ι] (W : ι → A.Opens) (s : ι → Set A)
    (hs : ∀ i, (s i).Finite) (hsW : ∀ i, s i ⊆ W i)
    (hsn : ∀ i, s i ⊆ exactRank (Over.mk p) n) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (b : ι → Γ(A, ⊤)),
      (∀ i, s i ⊆ A.basicOpen (b i)) ∧
      (∀ i, A.basicOpen (b i) ≤ W i) ∧
      (∀ i, A.basicOpen (b i) ≤ rankImageOpen (Over.mk p) n) ∧
      ∀ k i, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen (b i) ≤
        rankStageCore e n a ha k := by
  have hf : (⋃ i, s i).Finite := Set.finite_iUnion hs
  have hn : (⋃ i, s i) ⊆ exactRank (Over.mk p) n := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hsn i hi
  obtain ⟨a, ha, c, hc, hcU, hcore⟩ :=
    exists_rankStage_original_finite_neighborhood e n (⋃ i, s i) hf hn
  have hex i : ∃ b : Γ(A, ⊤), s i ⊆ A.basicOpen b ∧
      A.basicOpen b ≤ A.basicOpen c ⊓ W i := by
    apply AffineEnvelopeFiniteNeighborhood.exists_envelope_principal _ _ (hs i)
    intro x hx
    exact ⟨hc (Set.mem_iUnion.mpr ⟨i, hx⟩), hsW i hx⟩
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice hex
  refine ⟨a, ha, b, fun i ↦ (hb i).1, fun i ↦ (hb i).2.trans inf_le_right,
    fun i ↦ ((hb i).2.trans inf_le_left).trans hcU, fun k i ↦ ?_⟩
  exact ((TopologicalSpace.Opens.map (rankThickeningMap (Over.mk p) n k).base).monotone
    ((hb i).2.trans inf_le_left)).trans (hcore k)

/-- Full scalar fibers may be used as the chart sets when their entire images are finite. -/
theorem exists_rankStage_original_fiber_atlas (n : ℕ)
    {ι : Type} [Finite ι] {P : Type} (c : P)
    (T : ι → Type) (σ : ∀ i, T i → P) (g : ∀ i, T i → A)
    (W : ι → A.Opens)
    (hf : ∀ i, (g i '' (σ i ⁻¹' {c})).Finite)
    (hW : ∀ i x, σ i x = c → g i x ∈ W i)
    (hn : ∀ i x, σ i x = c → g i x ∈ exactRank (Over.mk p) n) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (b : ι → Γ(A, ⊤)),
      (∀ i x, σ i x = c → g i x ∈ A.basicOpen (b i)) ∧
      (∀ i, A.basicOpen (b i) ≤ W i) ∧
      (∀ i, A.basicOpen (b i) ≤ rankImageOpen (Over.mk p) n) ∧
      ∀ k i, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen (b i) ≤
        rankStageCore e n a ha k := by
  obtain ⟨a, ha, b, hb, hbW, hbU, hc⟩ := exists_rankStage_original_finite_atlas e n W
    (fun i ↦ g i '' (σ i ⁻¹' {c})) hf
    (fun i _ ⟨x, hx, he⟩ ↦ he ▸ hW i x hx)
    (fun i _ ⟨x, hx, he⟩ ↦ he ▸ hn i x hx)
  exact ⟨a, ha, b, fun i x hx ↦ hb i ⟨x, hx, rfl⟩, hbW, hbU, hc⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
