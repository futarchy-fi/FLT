/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousCochainScaledClass
public import FLT.Mazur.RankStageCoreCorrectionCriterion
public import FLT.Mazur.RankStageCoreCorrectionSpace
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# Choice independence of the actual original-boundary correction class

Full homogeneous changes of the local lifts leave the correction class
unchanged. A global boundary tower constructs actual whole-core corrections
and kills this class without any separate overlap extension hypothesis.
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
local instance boundaryClassOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryClassOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryClassOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n) (J : A.IdealSheafData)
local notation "C" j:max => rankStageCompatibleCoreInvariants e n (c j) (hc j)
local notation "I" j:max k:max => rankStageCoreBoundaryIdeal e n (c j) (hc j) J k
local notation "L" => rankStageCochainLeft e n c hc
local notation "R" => rankStageCochainRight e n c hc
local notation "K" => fun j ↦ rankStageCompatibleCoreBoundaryKernel e n (c j) (hc j) J
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition
  rankStageCompatibleCoreRefinement
  HomogeneousCochainCorrection.cochains HomogeneousCochainCorrection.difference
  HomogeneousCochainCorrection.correctionImage HomogeneousCochainCorrection.obstruction
  HomogeneousCochainCorrection.scalarIdeal

/-- The scalar action uses the unchanged original section at each full core order. -/
theorem rankStageOriginalCore_smul_val (j : ι) (s : compatibleFunctions p q)
    (v : C j) (k : ℕ) :
    ((s • v).val k).val = (rankStageCoreOriginalMap e n (c j) (hc j) k).appTop s.val *
      (v.val k).val := by
  change (rankStageGlobalCoreRestriction e n (c j) (hc j) k
    (rankStageOriginalInvariantRestriction e n k s)).val * (v.val k).val = _
  rw [rankStageGlobalCoreRestriction_val]
  rfl

/-- Scaled corrected lifts retain precisely the scaled full original boundary section. -/
theorem rankStageCoreCorrection_scaled_boundary (j : ι) (s : compatibleFunctions p q)
    (v h : C j) (t : Γ(J.subscheme, ⊤))
    (hv : ∀ k, (I j k).subschemeι.appTop (v.val k).val =
      (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t)
    (hh : ∀ k, (I j k).subschemeι.appTop (h.val k).val = 0) (k : ℕ) :
    (I j k).subschemeι.appTop (((s • v) - h).val k).val =
      (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop
        (J.subschemeι.appTop s.val * t) := by
  change (I j k).subschemeι.appTop (((s • v).val k).val - (h.val k).val) = _
  rw [map_sub, hh k, sub_zero, rankStageOriginalCore_smul_val, map_mul, hv k, map_mul]
  congr 1
  exact IdealSheafClosedTransitions.section_square _ _ _
    (rankStageCoreOriginalMap_ideal e n (c j) (hc j) J k) s.val

/-- An admissible original scalar kills the full correction class of the scaled lifts. -/
theorem mem_rankStageCoreCorrectionIdeal_iff_scaled_class
    (v : ∀ j, C j) (s : compatibleFunctions p q) :
    s ∈ rankStageCoreCorrectionIdeal e n c hc J v ↔
      rankStageCoreCorrectionObstruction e n c hc J (s • v) = 0 := by
  unfold rankStageCoreCorrectionIdeal rankStageCoreCorrectionObstruction
    rankStageCoreCorrectionClass
  exact HomogeneousCochainCorrection.mem_scalarIdeal_iff_scaled_obstruction L R K v s

/-- The same full boundary values give the same class, regardless of the local lift choices. -/
theorem rankStageCoreCorrectionObstruction_independent (v w : ∀ j, C j)
    (h : ∀ j k, (I j k).subschemeι.appTop ((v j).val k).val =
      (I j k).subschemeι.appTop ((w j).val k).val) :
    rankStageCoreCorrectionObstruction e n c hc J v =
      rankStageCoreCorrectionObstruction e n c hc J w := by
  unfold rankStageCoreCorrectionObstruction rankStageCoreCorrectionClass
  apply HomogeneousCochainCorrection.obstruction_eq_of_sub_mem L R K
  intro j k
  change (I j k).subschemeι.appTop (((v j).val k).val - ((w j).val k).val) = 0
  rw [map_sub, h j k, sub_self]

/-- The exact original scalar ideal is independent of all choices of full boundary lifts. -/
theorem rankStageCoreCorrectionIdeal_independent (v w : ∀ j, C j)
    (h : ∀ j k, (I j k).subschemeι.appTop ((v j).val k).val =
      (I j k).subschemeι.appTop ((w j).val k).val) :
    rankStageCoreCorrectionIdeal e n c hc J v = rankStageCoreCorrectionIdeal e n c hc J w := by
  unfold rankStageCoreCorrectionIdeal
  apply HomogeneousCochainCorrection.scalarIdeal_eq_of_sub_mem
  intro j k
  change (I j k).subschemeι.appTop (((v j).val k).val - ((w j).val k).val) = 0
  rw [map_sub, h j k, sub_self]

/-- One full global tower constructs a simultaneous homogeneous splitting on all whole cores. -/
theorem rankStageCoreCorrectionObstruction_eq_zero_of_global (v : ∀ j, C j)
    (w : rankStageCompatibleInvariants e n) (t : Γ(J.subscheme, ⊤))
    (hv : ∀ j k, (I j k).subschemeι.appTop ((v j).val k).val =
      (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t)
    (hw : ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (w.val k).val =
      (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t) :
    rankStageCoreCorrectionObstruction e n c hc J v = 0 := by
  rw [← one_mem_rankStageCoreCorrectionIdeal, mem_rankStageCoreCorrectionIdeal]
  simp only [one_smul]
  refine ⟨fun j ↦ rankStageGlobalBoundaryCoreCorrection e n (c j) (hc j) (v j) w,
    fun j k ↦ rankStageGlobalBoundaryCoreCorrection_boundary e n (c j) (hc j) J
      (v j) w t (hv j) hw k, ?_⟩
  intro i j k
  rw [rankStageGlobalBoundaryCoreCorrection_corrects,
    rankStageGlobalBoundaryCoreCorrection_corrects]
  exact rankStageGlobalCoreRestriction_overlap_zero e n (c i) (hc i) (c j) (hc j) k (w.val k)

end FLT.Mazur.EquivalenceRelationOrderedFrames
