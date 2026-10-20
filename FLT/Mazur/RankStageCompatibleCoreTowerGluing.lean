/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteCoreGluing

/-!
# Actual stage coefficients from compatible towers on finitely many cores

Sheaf gluing constructs the full invariant section at each order. Its
uniqueness forces every closed order transition, so the construction does
not discard the compatibility already present on the individual cores.
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
local instance towerGlueOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance towerGlueOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance towerGlueOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hcore : ∀ (c : C) k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.val.2 ≤
    rankStageCore e n c.val.1 (ha c) k)
  (hcover : exactRank (Over.mk p) n ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A))

include hcore hcover in
/-- The glued full coefficients retain compatibility at every pair of orders. -/
theorem exists_rankStage_invariant_tower_of_errors_zero
    (v : ∀ (c : C) k, rankStageCoreInvariants e n c.val.1 (ha c) k)
    (hv : ∀ (c d : C) k,
      rankStageInvariantOverlapError e n c.val.1 d.val.1 (ha c) (ha d) k (v c k) (v d k) = 0)
    (ht : ∀ (c : C) k l (hkl : k ≤ l),
      rankStageCoreRestriction e n c.val.1 (ha c) hkl (v c l) = v c k) :
    ∃ t : ∀ k, compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k),
      (∀ (c : C) k, (rankStageCore e n c.val.1 (ha c) k).ι.appTop (t k).val =
        (v c k).val) ∧
      ∀ k l (hkl : k ≤ l),
        (rankStageTransition (Over.mk p) n hkl).appTop (t l).val = (t k).val := by
  have hex (k : ℕ) := existsUnique_rankStage_invariant_of_errors_zero e n C ha hcore hcover
    k (fun c ↦ v c k) (fun c d ↦ hv c d k)
  choose t ht' hu using hex
  refine ⟨t, fun c k ↦ ht' k c, fun k l hkl ↦ ?_⟩
  apply section_ext (fun c : C ↦ rankStageCore e n c.val.1 (ha c) k)
    (rankStage_finite_core_cover e n C ha hcore hcover k)
  intro c
  rw [ht' k c]
  change ((rankStageCore e n c.val.1 (ha c) k).ι ≫
    rankStageTransition (Over.mk p) n hkl).appTop (t l).val = _
  rw [← rankStageCoreMap_inclusion]
  change (rankStageCoreMap e n c.val.1 (ha c) hkl).appTop
    ((rankStageCore e n c.val.1 (ha c) l).ι.appTop (t l).val) = _
  rw [ht' l c]
  exact congrArg Subtype.val (ht c k l hkl)

end FLT.Mazur.EquivalenceRelationOrderedFrames
