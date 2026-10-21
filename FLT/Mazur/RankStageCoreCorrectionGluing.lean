/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryCorrectionClass
public import FLT.Mazur.RankStageCompatibleCoreTowerGluing
public import FLT.Mazur.OpenCoverFullBoundaryDetection

/-!
# Exact gluing criterion for the genuine compatible correction class

On the constructed finite core cover, vanishing is equivalent to existence
of a global compatible full boundary tower. Gluing preserves the unchanged
boundary ideal at every order; no affineness of the full stages is needed.
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
local instance correctionGlueOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance correctionGlueOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance correctionGlueOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hc : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hcore : ∀ (c : C) k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.val.2 ≤
    rankStageCore e n c.val.1 (hc c) k)
  (hcover : exactRank (Over.mk p) n ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A))
  (J : A.IdealSheafData)
local notation "a" => fun c : C ↦ Prod.fst (Subtype.val c)
local notation "U" c:max k:max => rankStageCore e n (Prod.fst (Subtype.val c)) (hc c) k
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition rankStageCoreCorrectionObstruction

include hcore hcover in
/-- Homogeneous corrected finite-core towers glue with their full original boundary values. -/
theorem exists_rankStage_full_boundary_tower_of_correction_zero
    (v : ∀ c : C, rankStageCompatibleCoreInvariants e n c.val.1 (hc c))
    (t : Γ(J.subscheme, ⊤))
    (hv : ∀ c k, (rankStageCoreBoundaryIdeal e n c.val.1 (hc c) J k).subschemeι.appTop
      ((v c).val k).val = (rankStageCoreOriginalBoundaryMap e n c.val.1 (hc c) J k).appTop t)
    (hz : rankStageCoreCorrectionObstruction e n a hc J v = 0) :
    ∃ w : rankStageCompatibleInvariants e n,
      ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (w.val k).val =
        (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t := by
  have hm := (one_mem_rankStageCoreCorrectionIdeal e n a hc J v).mpr hz
  obtain ⟨h, hh, he⟩ := (mem_rankStageCoreCorrectionIdeal e n a hc J v 1).mp hm
  simp only [one_smul] at he
  let u (c : C) := v c - h c
  obtain ⟨w, hw, ht⟩ := exists_rankStage_invariant_tower_of_errors_zero e n C hc hcore hcover
    (fun c k ↦ (u c).val k) he (fun c k l hkl ↦ (u c).property k l hkl)
  have hwc : ∀ k l (hkl : k ≤ l), rankStageInvariantTransition e n hkl (w l) = w k := by
    intro k l hkl
    apply Subtype.ext
    rw [rankStageInvariantTransition_val]
    exact ht k l hkl
  refine ⟨⟨w, hwc⟩, fun k ↦ ?_⟩
  apply OpenCoverFullBoundaryDetection.boundary_eq_of_local (fun c : C ↦ U c k)
    (rankStage_finite_core_cover e n C hc hcore hcover k)
    (rankStageBoundaryIdeal (p := p) n k J) (w k).val
    ((rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t)
  intro c
  rw [hw c k]
  change (rankStageCoreBoundaryIdeal e n c.val.1 (hc c) J k).subschemeι.appTop
    (((v c).val k).val - ((h c).val k).val) = _
  rw [map_sub]
  refine (congrArg₂ (fun x y ↦ x - y) (hv c k) (hh c k)).trans ?_
  rw [sub_zero]
  change (rankStageCoreOriginalBoundaryMap e n c.val.1 (hc c) J k).appTop t =
    (IdealSheafClosedTransitions.map _ _ (U c k).ι rfl ≫
      rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t
  rw [rankStageCoreBoundary_full_map]
  rfl

include hcore hcover in
/-- Admissible original scalars give global towers of the exact scaled original boundary. -/
theorem exists_rankStage_scaled_full_boundary_tower_of_correction
    (v : ∀ c : C, rankStageCompatibleCoreInvariants e n c.val.1 (hc c))
    (t : Γ(J.subscheme, ⊤))
    (hv : ∀ c k, (rankStageCoreBoundaryIdeal e n c.val.1 (hc c) J k).subschemeι.appTop
      ((v c).val k).val = (rankStageCoreOriginalBoundaryMap e n c.val.1 (hc c) J k).appTop t)
    (s : compatibleFunctions p q) (hs : s ∈ rankStageCoreCorrectionIdeal e n a hc J v) :
    ∃ w : rankStageCompatibleInvariants e n,
      ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (w.val k).val =
        (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop
          (J.subschemeι.appTop s.val * t) := by
  apply exists_rankStage_full_boundary_tower_of_correction_zero e n C hc hcore hcover J (s • v)
    (J.subschemeι.appTop s.val * t)
  · intro c k
    simpa only [Pi.smul_apply, sub_zero] using
      rankStageCoreCorrection_scaled_boundary e n a hc J c s
        (v c) 0 t (hv c) (fun _ ↦ map_zero _) k
  · exact (mem_rankStageCoreCorrectionIdeal_iff_scaled_class e n a hc J v s).mp hs

include hcore hcover in
/-- The genuine class vanishes exactly when the full compatible boundary problem has a solution. -/
theorem rankStageCoreCorrectionObstruction_eq_zero_iff_global
    (v : ∀ c : C, rankStageCompatibleCoreInvariants e n c.val.1 (hc c))
    (t : Γ(J.subscheme, ⊤))
    (hv : ∀ c k, (rankStageCoreBoundaryIdeal e n c.val.1 (hc c) J k).subschemeι.appTop
      ((v c).val k).val = (rankStageCoreOriginalBoundaryMap e n c.val.1 (hc c) J k).appTop t) :
    rankStageCoreCorrectionObstruction e n a hc J v = 0 ↔
      ∃ w : rankStageCompatibleInvariants e n,
        ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (w.val k).val =
          (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t := by
  constructor
  · exact exists_rankStage_full_boundary_tower_of_correction_zero e n C hc hcore hcover J v t hv
  · rintro ⟨w, hw⟩
    exact rankStageCoreCorrectionObstruction_eq_zero_of_global e n a hc J v w t hv hw

end FLT.Mazur.EquivalenceRelationOrderedFrames
