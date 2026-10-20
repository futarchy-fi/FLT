/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenCoefficientGluing
public import FLT.Mazur.RankStageFiniteCoreCover
public import FLT.Mazur.RankStageInvariantOverlapCocycle

/-!
# Gluing compatible coefficients on the actual finite rank-stage cover

The original finite principal cover constructs a cover by full invariant
cores at every order. Vanishing of the actual product-core errors gives a
unique full invariant section on the rank stage. This is stagewise gluing,
not algebraization of a tower or gluing between different ranks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections InvariantOpenCoefficientGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance glueOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance glueOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance glueOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore
/-- Equality on a named overlap is equality on the literal intersection. -/
private theorem overlap_eq_of_eq_domain {X : Scheme.{0}} (U V W : X.Opens)
    (hW : W = U ⊓ V) (hU : W ≤ U) (hV : W ≤ V)
    (s : Γ(U.toScheme, ⊤)) (t : Γ(V.toScheme, ⊤))
    (h : (X.homOfLE hU).appTop s = (X.homOfLE hV).appTop t) :
    (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).appTop s =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).appTop t := by
  subst W
  exact h

variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hcore : ∀ (c : C) k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.val.2 ≤
    rankStageCore e n c.val.1 (ha c) k)
  (hcover : exactRank (Over.mk p) n ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A))

include hcore hcover in
/-- The selected whole-orbit cores cover every full rank thickening. -/
theorem rankStage_finite_core_cover (k : ℕ) :
    (⨆ c : C, rankStageCore e n c.val.1 (ha c) k) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨c, hc, hy⟩ := Set.mem_iUnion₂.mp
    (hcover ((rankThickeningMap_range (Over.mk p) n k).le ⟨y, rfl⟩))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨c, hc⟩, hcore ⟨c, hc⟩ k hy⟩

include hcore hcover in
/-- Zero product-core errors give an actual invariant section on the entire stage. -/
theorem existsUnique_rankStage_invariant_of_errors_zero (k : ℕ)
    (v : ∀ c : C, rankStageCoreInvariants e n c.val.1 (ha c) k)
    (hv : ∀ c d : C,
      rankStageInvariantOverlapError e n c.val.1 d.val.1 (ha c) (ha d) k (v c) (v d) = 0) :
    ∃! t : compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k),
      ∀ c : C, (rankStageCore e n c.val.1 (ha c) k).ι.appTop t.val = (v c).val := by
  apply existsUnique_invariant _ _ (fun c : C ↦ rankStageCore e n c.val.1 (ha c) k)
    (fun c ↦ rankStageCore_invariant e n c.val.1 (ha c) k)
    (rankStage_finite_core_cover e n C ha hcore hcover k) v
  intro c d
  apply Subtype.ext
  have he := congrArg Subtype.val (sub_eq_zero.mp (hv c d))
  simp only [rankStageCoreRefinement_val] at he
  exact overlap_eq_of_eq_domain _ _ _
    (rankStageCore_mul e n c.val.1 d.val.1 (ha c) (ha d) k) _ _ _ _ he

/-- Finitely many named affine invariant cores cover all orders of an entire rank stage. -/
theorem exists_rankStage_finite_core_cover :
    ∃ (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
      (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n),
      ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (ha c) k) = ⊤ := by
  obtain ⟨C, hC, hcover⟩ := exists_rankStage_original_finite_core_cover e n ⊤
    (exactRank (Over.mk p) n) (Set.subset_univ _) (Set.Subset.refl _)
  have hex (c : C) := hC c.val c.property
  choose ha hW hb hc using hex
  exact ⟨C, ha, rankStage_finite_core_cover e n C ha hc hcover⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
