/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageRelativeClosedCoreProduct

/-!
# Actual boundary overlap control without a finite original projection

When higher ranks are relatively closed, original scalars defining the
pairwise cores give a common annihilator for the actual boundary errors.
The errors are constructed from the original boundary section and all
full homogeneous boundary and transition equations are retained.
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
local instance boundaryRelativeOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryRelativeOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryRelativeOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)
  (hn : IsClosed ((rankImageOpen (Over.mk p) n).ι ⁻¹'
    (rankImageOpen (Over.mk p) (n + 1) : Set A)))
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
  {ι : Type*} [Fintype ι] (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
local notation "v" j:max =>
  rankStageChosenBoundaryCoreTower e n (c j) (hc j) J hJ f hf t
local notation "a" j:max => c j.1 * c j.2
local notation "ha" j:max =>
  rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)
local notation "x" j:max => rankStageCompatibleOverlapError e n
  (c j.1) (c j.2)
  (hc j.1) (hc j.2) (v j.1) (v j.2)
variable (s : ι × ι → compatibleFunctions p q)
  (hcore : ∀ (j : ι × ι) k, rankStageCore e n (c j.1 * c j.2)
    (rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)) k =
    (rankThickening (Over.mk p) n k).basicOpen
      (rankStageOriginalInvariantRestriction e n k (s j)).val)
attribute [local irreducible] rankStageCore rankStageCompatibleOverlapError
  rankStageChosenBoundaryCoreTower rankStageGlobalBoundaryKernel
  rankStageOriginalNumeratorIdeal rankStageInvariantTransition rankStageGlobalCoreRestriction

include hn hcore in
/-- Actual original-boundary errors have a common annihilator in the unchanged invariant ring. -/
theorem rankStageBoundaryCoreProduct_mem_radical_of_next_relatively_closed :
    (∏ j, s j) ∈
      (rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t
        c hc).radical := by
  exact rankStageOriginalCoreProduct_mem_radical_of_next_relatively_closed
    e f hf (fun _ : ι × ι ↦ n)
    (fun j ↦ a j) (fun j ↦ ha j) (fun _ ↦ hn) s hcore J (fun j ↦ x j)
    (fun j ↦ rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t
      c hc j.1 j.2)

include hn hcore in
/-- The constructed common original scalar gives compatible full homogeneous overlap numerators. -/
theorem exists_rankStageBoundaryCoreProduct_uniform_of_next_relatively_closed :
    ∃ (N : ℕ) (w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
      ∀ (j : ι × ι) k, rankStageGlobalCoreRestriction e n (a j) (ha j) k (w j k) =
        (rankStageGlobalCoreRestriction e n (a j) (ha j) k
          (rankStageOriginalInvariantRestriction e n k
            (∏ j, s j))) ^ N *
            (x j).val k := by
  exact exists_rankStageOriginalCoreProduct_uniform_of_next_relatively_closed
    e f hf (fun _ : ι × ι ↦ n)
    (fun j ↦ a j) (fun j ↦ ha j) (fun _ ↦ hn) s hcore J (fun j ↦ x j)
    (fun j ↦ rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t
      c hc j.1 j.2)

end FLT.Mazur.EquivalenceRelationOrderedFrames
