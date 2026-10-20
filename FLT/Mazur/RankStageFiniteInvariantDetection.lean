/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreInvariantDetection

/-!
# Constructed finite families detecting the full original invariant ring

Noetherian compactness and the original rank bound construct finitely many
core families. Testing every order in these families characterizes the actual
original invariant subring, including nilpotents and lower-rank points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteInvariantOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteInvariantOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteInvariantOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore rankStageCoreOriginalMap

/-- Finitely many constructed core families detect membership in the full invariant ring. -/
theorem exists_finite_original_invariant_detection :
    ∃ (N : ℕ) (C : Fin (N + 1) → Finset (Γ(A, ⊤) × Γ(A, ⊤)))
      (ha : ∀ n (c : C n), A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n.val),
      (∀ n (c : C n) order,
        rankThickeningMap (Over.mk p) n.val order ⁻¹ᵁ A.basicOpen c.val.2 ≤
          rankStageCore e n.val c.val.1 (ha n c) order) ∧
      ∀ s : Γ(A, ⊤), s ∈ compatibleFunctions p q ↔
        ∀ n (c : C n) order,
          (rankStageCoreOriginalMap e n.val c.val.1 (ha n c) order).appTop s ∈
            rankStageCoreInvariants e n.val c.val.1 (ha n c) order := by
  classical
  obtain ⟨N, C, hC, hcover⟩ := exists_rankStage_bounded_original_core_cover e ⊤
  have hex (n : Fin (N + 1)) (c : C n) := hC n c.val c.property
  choose ha hW hb hc using hex
  refine ⟨N, C, ha, hc, fun s ↦ ?_⟩
  constructor
  · intro hs n c order
    exact original_invariant_mem_core e n.val c.val.1 (ha n c) order s hs
  · intro hs
    apply original_invariant_of_core_orders e
      (fun i : Σ n, C n ↦ i.1.val) (fun i ↦ i.2.val.1) (fun i ↦ i.2.val.2)
      (fun i ↦ ha i.1 i.2) (fun i ↦ hc i.1 i.2) ?_ s (fun i ↦ hs i.1 i.2)
    intro x
    obtain ⟨n, hn, c, hmem, hxc⟩ := hcover x trivial
    exact ⟨⟨n, ⟨c, hmem⟩⟩, hn, hxc⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
