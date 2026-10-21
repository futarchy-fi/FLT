/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreCorrectionCokernel

/-!
# Exact compatible rank-core correction criteria

Every source coordinate is a homogeneous compatible tower on a whole core.
The map takes its actual coboundary on every overlap. Thus the distinguished
class tests simultaneous cochain splitting, including all order equations.
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
local instance correctionCriterionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance correctionCriterionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance correctionCriterionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
local notation "C" j:max => rankStageCompatibleCoreInvariants e n (c j) (hc j)
local notation "O" i:max j:max => rankStageCompatibleCoreInvariants e n (c i * c j)
  (rankStageProduct_domain n (c i) (c j) (hc i))
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition
  rankStageCompatibleCoreRefinement
  HomogeneousCochainCorrection.cochains HomogeneousCochainCorrection.difference
  HomogeneousCochainCorrection.correctionImage HomogeneousCochainCorrection.obstruction
  HomogeneousCochainCorrection.scalarIdeal

variable (J : A.IdealSheafData)
local notation "L" => rankStageCochainLeft e n c hc
local notation "R" => rankStageCochainRight e n c hc
local notation "K" => fun j ↦ rankStageCompatibleCoreBoundaryKernel e n (c j) (hc j) J

/-- Membership constructs one homogeneous cochain with exact corrected overlaps at every order. -/
theorem mem_rankStageCoreCorrectionIdeal (v : ∀ j, C j) (s : compatibleFunctions p q) :
    s ∈ rankStageCoreCorrectionIdeal e n c hc J v ↔
      ∃ h : ∀ j, C j,
        (∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
          ((h j).val k).val = 0) ∧
        ∀ i j k, rankStageInvariantOverlapError e n (c i) (c j) (hc i) (hc j) k
          (((s • v i) - h i).val k) (((s • v j) - h j).val k) = 0 := by
  unfold rankStageCoreCorrectionIdeal
  rw [HomogeneousCochainCorrection.mem_scalarIdeal_iff_corrections]
  constructor
  · rintro ⟨h, hh, he⟩
    refine ⟨h, hh, fun i j k ↦ ?_⟩
    have hval := congrArg (fun z : O i j ↦ z.val k) (he i j)
    simp only [rankStageCochainLeft, rankStageCochainRight,
      rankStageCompatibleCoreRefinement_val] at hval
    exact sub_eq_zero.mpr hval
  · rintro ⟨h, hh, he⟩
    refine ⟨h, hh, fun i j ↦ ?_⟩
    apply Subtype.ext
    funext k
    simp only [rankStageCochainLeft, rankStageCochainRight,
      rankStageCompatibleCoreRefinement_val]
    exact sub_eq_zero.mp (he i j k)

end FLT.Mazur.EquivalenceRelationOrderedFrames
