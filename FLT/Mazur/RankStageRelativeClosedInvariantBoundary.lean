/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageRelativeClosedBoundaryProduct

/-!
# Invariant boundary chart products under relative rank closedness

Invariant original parameters define the actual cores automatically.
Consequently the unchanged pairwise parameter product annihilates the
constructed original-boundary overlap obstruction, without a core equation
hypothesis or a finite original projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance invariantRelativeOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance invariantRelativeOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance invariantRelativeOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)
  (hn : IsClosed ((rankImageOpen (Over.mk p) n).ι ⁻¹'
    (rankImageOpen (Over.mk p) (n + 1) : Set A)))
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
  {ι : Type*} [Fintype ι] (c : ι → compatibleFunctions p q)
  (hc : ∀ j, A.basicOpen (c j).val ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "v" j:max =>
  rankStageChosenBoundaryCoreTower e n (c j).val (hc j) J hJ f hf t
local notation "a" j:max => (c j.1).val * (c j.2).val
local notation "ha" j:max =>
  rankStageProduct_domain n (c j.1).val (c j.2).val (hc j.1)
local notation "x" j:max => rankStageCompatibleOverlapError e n
  (c j.1).val (c j.2).val
  (hc j.1) (hc j.2) (v j.1) (v j.2)
attribute [local irreducible] rankStageCore rankStageCompatibleOverlapError
  rankStageChosenBoundaryCoreTower rankStageGlobalBoundaryKernel
  rankStageOriginalNumeratorIdeal rankStageInvariantTransition rankStageGlobalCoreRestriction

include hn in
/-- Actual original-boundary errors have a common annihilator in the unchanged invariant ring. -/
theorem rankStageBoundaryInvariantProduct_mem_radical_of_next_relatively_closed :
    (∏ j : ι × ι, c j.1 * c j.2) ∈
      (rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t
        (fun j ↦ (c j).val) hc).radical := by
  exact rankStageBoundaryCoreProduct_mem_radical_of_next_relatively_closed
    e n hn J hJ f hf t (fun j ↦ (c j).val) hc (fun j ↦ c j.1 * c j.2)
    (fun j ↦ rankStageCore_eq_basicOpen_original e n (c j.1 * c j.2) (ha j))

include hn in
/-- The constructed common original scalar gives compatible full homogeneous overlap numerators. -/
theorem exists_rankStageBoundaryInvariantProduct_uniform_of_next_relatively_closed :
    ∃ (N : ℕ) (w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
      ∀ (j : ι × ι) k, rankStageGlobalCoreRestriction e n (a j) (ha j) k (w j k) =
        (rankStageGlobalCoreRestriction e n (a j) (ha j) k
          (rankStageOriginalInvariantRestriction e n k
            (∏ j : ι × ι, c j.1 * c j.2))) ^ N *
            (x j).val k := by
  exact exists_rankStageBoundaryCoreProduct_uniform_of_next_relatively_closed
    e n hn J hJ f hf t (fun j ↦ (c j).val) hc (fun j ↦ c j.1 * c j.2)
    (fun j ↦ rankStageCore_eq_basicOpen_original e n (c j.1 * c j.2) (ha j))

end FLT.Mazur.EquivalenceRelationOrderedFrames
