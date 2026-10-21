/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageAffineBoundaryCoreSelection

/-!
# Vanishing of the corrected original-scalar overlap obstruction

The actual chosen original-boundary towers are modified by the constructed
full homogeneous core corrections. Their new overlap ideal is the unit ideal
in the unchanged original invariant ring. No claim is made for the numerator
ideal of the uncorrected arbitrary local towers.
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
local instance correctedObstructionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance correctedObstructionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance correctedObstructionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  [∀ k, IsAffine (rankThickening (Over.mk p) n k)]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
  {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
local notation "v" j:max => rankStageChosenBoundaryCoreTower e n (c j) (hc j) J hJ f hf t
local notation "δ" j:max => rankStageAffineBoundaryCorrection e n J hJ f hf t (c j) (hc j)
local notation "w" => rankStageAffineChosenBoundaryTower e n J hJ f hf t
attribute [local irreducible] rankStageCore rankStageGlobalCoreRestriction
  rankStageInvariantTransition rankStageChosenBoundaryCoreTower rankStageAffineBoundaryCorrection

/-- The corrected tower retains the prescribed full original boundary on every chart. -/
theorem rankStageAffine_corrected_boundary (j : ι) (k : ℕ) :
    (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
        (((v j) - (δ j)).val k).val =
      (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t.val := by
  rw [rankStageAffineBoundaryCorrection_corrects]
  exact rankStageGlobalCoreRestriction_boundary e n (c j) (hc j) J k ((w).val k) t.val
    (rankStageAffineChosenBoundaryTower_boundary e n J hJ f hf t k)

/-- The actual corrected towers agree on every full overlap at every order. -/
theorem rankStageAffine_corrected_overlap_zero (i j : ι) (k : ℕ) :
    rankStageInvariantOverlapError e n (c i) (c j) (hc i) (hc j) k
      (((v i) - (δ i)).val k) (((v j) - (δ j)).val k) = 0 := by
  rw [rankStageAffineBoundaryCorrection_corrects, rankStageAffineBoundaryCorrection_corrects]
  exact rankStageGlobalCoreRestriction_overlap_zero e n (c i) (hc i) (c j) (hc j) k ((w).val k)

/-- The corrected all-order obstruction vanishes over the unchanged original scalar ring. -/
theorem rankStageAffine_corrected_overlapIdeal_eq_top :
    rankStageOverlapNumeratorIdeal e n c hc J (fun j ↦ (v j) - (δ j)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [one_mem_rankStageOverlapNumeratorIdeal]
  refine ⟨fun _ _ ↦ 0, fun _ _ ↦ Ideal.zero_mem _, fun _ _ _ _ ↦ map_zero _, ?_⟩
  intro j k
  rw [map_zero, rankStageAffine_corrected_overlap_zero]

end FLT.Mazur.EquivalenceRelationOrderedFrames
