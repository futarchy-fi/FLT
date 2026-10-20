/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalProductAnnihilation

/-!
# Constructed original-scalar annihilation of actual boundary overlap errors

For a finite collection of original invariant principal domains, the
product of their pairwise parameters annihilates the actual chosen overlap
vector by one power at every order. A closed higher-frame locus suffices;
its emptiness is unnecessary. The scalar is not asserted to be a unit.
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
local instance originalOverlapProductOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalOverlapProductOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalOverlapProductOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (hn : IsClosed (rankImageOpen (Over.mk p) (n + 1) : Set A))
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
  {ι : Type*} [Fintype ι] (c : ι → compatibleFunctions p q)
  (hc : ∀ j, A.basicOpen (c j).val ≤ rankImageOpen (Over.mk p) n)
local notation "v" j:max =>
  rankStageChosenBoundaryCoreTower e n (Subtype.val (c j)) (hc j) J hJ f hf t
local notation "a" j:max => c j.1 * c j.2
local notation "ha" j:max =>
  rankStageProduct_domain n (Subtype.val (c j.1)) (Subtype.val (c j.2)) (hc j.1)
local notation "x" j:max => rankStageCompatibleOverlapError e n
  (Subtype.val (c j.1)) (Subtype.val (c j.2))
  (hc j.1) (hc j.2) (v j.1) (v j.2)
attribute [local irreducible] rankStageCore rankStageCompatibleOverlapError
  rankStageChosenBoundaryCoreTower rankStageGlobalBoundaryKernel
  rankStageOriginalNumeratorIdeal rankStageInvariantTransition rankStageGlobalCoreRestriction

include hn in
/-- Actual original-boundary errors have a common annihilator in the unchanged invariant ring. -/
theorem rankStageOriginalBoundaryProduct_mem_radical :
    (∏ j : ι × ι, a j) ∈
      (rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t
        (fun j ↦ (c j).val) hc).radical := by
  exact rankStageOriginalProduct_mem_radical e f hf (fun _ : ι × ι ↦ n) (fun _ ↦ hn)
    (fun j ↦ a j) (fun j ↦ ha j) J (fun j ↦ x j)
    (fun j ↦ rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t
      (fun j ↦ (c j).val) hc j.1 j.2)

include hn in
/-- The constructed common original scalar gives compatible full homogeneous overlap numerators. -/
theorem exists_rankStageOriginalBoundaryProduct_uniform :
    ∃ (N : ℕ) (w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
      ∀ (j : ι × ι) k, rankStageGlobalCoreRestriction e n (a j).val (ha j) k (w j k) =
        (rankStageGlobalCoreRestriction e n (a j).val (ha j) k
          (rankStageOriginalInvariantRestriction e n k (∏ j : ι × ι, a j))) ^ N *
            (x j).val k := by
  exact exists_rankStageOriginalProduct_uniform e f hf (fun _ : ι × ι ↦ n) (fun _ ↦ hn)
    (fun j ↦ a j) (fun j ↦ ha j) J (fun j ↦ x j)
    (fun j ↦ rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t
      (fun j ↦ (c j).val) hc j.1 j.2)

end FLT.Mazur.EquivalenceRelationOrderedFrames
