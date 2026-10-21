/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryCorrectionClass
public import FLT.Mazur.RankStageAffineFullBoundaryTower
public import FLT.Mazur.RankStageClopenCoverBoundaryTower

/-!
# Geometric vanishing of the actual compatible cochain obstruction

Affine full thickenings or a finite clopen cover construct a global boundary
tower and therefore kill the genuine correction class of any chosen core
lifts. No pairwise global numerator condition is substituted for splitting.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance vanishClassOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance vanishClassOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance vanishClassOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
  (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))
  (hv : ∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
    ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t.val)
attribute [local irreducible] rankStageCore rankStageCoreRestriction rankStageInvariantTransition
  rankStageCoreCorrectionObstruction rankStageCoreCorrectionIdeal rankStageGlobalCoreRestriction

include hf hv in
/-- Affine full stages kill the actual compatible correction class for arbitrary core choices. -/
theorem rankStageCoreCorrectionObstruction_eq_zero_of_affine
    [∀ k, IsAffine (rankThickening (Over.mk p) n k)] :
    rankStageCoreCorrectionObstruction e n c hc J v = 0 := by
  obtain ⟨w, hw, hb⟩ := exists_rankStage_affine_full_original_boundary_tower e n J hJ f hf t
  exact rankStageCoreCorrectionObstruction_eq_zero_of_global e n c hc J v ⟨w, hw⟩ t.val hv hb

include hf hv in
/-- A finite clopen cover kills the class on any family of whole cores, including nonclopen ones. -/
theorem rankStageCoreCorrectionObstruction_eq_zero_of_clopen_cover
    {m : ℕ} (a : Fin m → Γ(A, ⊤))
    (ha : ∀ i, A.basicOpen (a i) ≤ rankImageOpen (Over.mk p) n)
    (hclosed : ∀ i,
      IsClosed (rankStageCore e n (a i) (ha i) 0 : Set (rankThickening (Over.mk p) n 0)))
    (hcover : (⨆ i, rankStageCore e n (a i) (ha i) 0) = ⊤) :
    rankStageCoreCorrectionObstruction e n c hc J v = 0 := by
  obtain ⟨w, hw, hb⟩ :=
    exists_rankStage_clopen_cover_boundary_tower e n a ha hclosed hcover J hJ f hf t
  exact rankStageCoreCorrectionObstruction_eq_zero_of_global e n c hc J v ⟨w, hw⟩ t.val hv hb

include hf in
/-- The actual independently chosen original-boundary lifts have unit correction ideal if affine. -/
theorem rankStageChosenCoreCorrectionIdeal_eq_top_of_affine
    [∀ k, IsAffine (rankThickening (Over.mk p) n k)] :
    rankStageCoreCorrectionIdeal e n c hc J
      (fun j ↦ rankStageChosenBoundaryCoreTower e n (c j) (hc j) J hJ f hf t) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [one_mem_rankStageCoreCorrectionIdeal]
  exact rankStageCoreCorrectionObstruction_eq_zero_of_affine e n c hc J hJ f hf t _
    (fun j ↦ rankStageChosenBoundaryCoreTower_boundary e n (c j) (hc j) J hJ f hf t)

end FLT.Mazur.EquivalenceRelationOrderedFrames
