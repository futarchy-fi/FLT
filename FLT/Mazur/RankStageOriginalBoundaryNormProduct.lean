/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalNormProduct

/-!
# Original norm control of actual arbitrary-chart boundary overlap errors

For a finite original relation, arbitrary original chart parameters give
one constructed invariant norm product and one exponent for all actual
boundary overlap errors. All rank orders and full homogeneous equations
are retained. Neither invariant input parameters nor closedness is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections FiniteFlatRelationNormCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] [IsFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryNormOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryNormOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryNormOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)
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
attribute [local irreducible] rankStageCore rankStageCompatibleOverlapError
  rankStageChosenBoundaryCoreTower rankStageGlobalBoundaryKernel
  rankStageOriginalNumeratorIdeal rankStageInvariantTransition rankStageGlobalCoreRestriction

/-- Actual original-boundary errors have a common annihilator in the unchanged invariant ring. -/
theorem rankStageOriginalBoundaryNormProduct_mem_radical :
    (∏ j : ι × ι, rankStageOriginalNorm e (a j)) ∈
      (rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t
        c hc).radical := by
  exact rankStageOriginalNormProduct_mem_radical e f hf (fun _ : ι × ι ↦ n)
    (fun j ↦ a j) (fun j ↦ ha j) J (fun j ↦ x j)
    (fun j ↦ rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t
      c hc j.1 j.2)

/-- The constructed common original scalar gives compatible full homogeneous overlap numerators. -/
theorem exists_rankStageOriginalBoundaryNormProduct_uniform :
    ∃ (N : ℕ) (w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
      ∀ (j : ι × ι) k, rankStageGlobalCoreRestriction e n (a j) (ha j) k (w j k) =
        (rankStageGlobalCoreRestriction e n (a j) (ha j) k
          (rankStageOriginalInvariantRestriction e n k
            (∏ j : ι × ι, rankStageOriginalNorm e (a j)))) ^ N *
            (x j).val k := by
  exact exists_rankStageOriginalNormProduct_uniform e f hf (fun _ : ι × ι ↦ n)
    (fun j ↦ a j) (fun j ↦ ha j) J (fun j ↦ x j)
    (fun j ↦ rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t
      c hc j.1 j.2)

end FLT.Mazur.EquivalenceRelationOrderedFrames
