/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationInvariantNeighborhoods
public import FLT.Mazur.RankStageOriginalPrincipalNumerators

/-!
# An original invariant principal atlas for every finite-relation rank

The finite original relation constructs finitely many original invariant
scalars covering the entire rank-image open. Their unchanged whole-orbit
cores cover every rank thickening. This is actual nonvanishing coverage,
not a claim that a product of the parameters is a unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] [IsFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finitePrincipalAtlasOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finitePrincipalAtlasOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finitePrincipalAtlasOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
omit [Etale q] in
/-- Original invariant parameters cover the full original rank-image open. -/
theorem exists_rankImage_original_invariant_cover (n : ℕ) :
    ∃ T : Finset (compatibleFunctions p q),
      (∀ s : T, A.basicOpen s.val.val ≤ rankImageOpen (Over.mk p) n) ∧
      (⨆ s : T, A.basicOpen s.val.val) = rankImageOpen (Over.mk p) n := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨T, hT, hc⟩ := FiniteRelationInvariantNeighborhoods.exists_finite_principal_cover
    p q e (rankImageOpen (Over.mk p) n) (rankImage_preimage_eq e n)
    (NoetherianSpace.isCompact _)
  exact ⟨T, fun s ↦ hT s.val s.property, hc⟩

attribute [local irreducible] rankStageCore

/-- One constructed original invariant atlas covers all full orders with unchanged parameters. -/
theorem exists_rankStage_original_invariant_atlas (n : ℕ) :
    ∃ (T : Finset (compatibleFunctions p q))
      (hT : ∀ s : T, A.basicOpen s.val.val ≤ rankImageOpen (Over.mk p) n),
      (⨆ s : T, A.basicOpen s.val.val) = rankImageOpen (Over.mk p) n ∧
      ∀ k, (⨆ s : T, rankStageCore e n s.val.val (hT s) k) = ⊤ := by
  obtain ⟨T, hT, hc⟩ := exists_rankImage_original_invariant_cover e n
  refine ⟨T, hT, hc, fun k ↦ eq_top_iff.mpr ?_⟩
  intro x _
  have hx : rankThickeningMap (Over.mk p) n k x ∈ rankImageOpen (Over.mk p) n :=
    ((rankThickeningMap_range (Over.mk p) n k).le ⟨x, rfl⟩).1
  rw [← hc] at hx
  obtain ⟨s, hs⟩ := Opens.mem_iSup.mp hx
  apply Opens.mem_iSup.mpr
  refine ⟨s, ?_⟩
  rw [rankStageCore_eq_basicOpen_original]
  change x ∈ (rankThickening (Over.mk p) n k).basicOpen
    ((rankThickeningMap (Over.mk p) n k).appTop s.val.val)
  rw [← Scheme.preimage_basicOpen_top]
  exact hs

end FLT.Mazur.EquivalenceRelationOrderedFrames
