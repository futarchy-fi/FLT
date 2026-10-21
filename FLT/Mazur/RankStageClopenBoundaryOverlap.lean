/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageClopenCoreObstruction
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# Actual original-boundary overlaps on clopen rank cores

The original boundary section constructs the local towers. When their
pairwise cores are closed inside the rank support, extension by zero gives
unscaled full homogeneous compatible overlap numerators. The original scalar
obstruction is then exactly the unit ideal, even without stable rank powers.
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
local instance clopenOverlapOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance clopenOverlapOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance clopenOverlapOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
  {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "v" j:max => rankStageChosenBoundaryCoreTower e n (c j) (hc j) J hJ f hf t
local notation "a" j:max => c j.1 * c j.2
local notation "ha" j:max => rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)
local notation "x" j:max => rankStageCompatibleOverlapError e n (c j.1) (c j.2)
  (hc j.1) (hc j.2) (v j.1) (v j.2)
variable (hclosed : ∀ j : ι × ι,
  IsClosed (rankStageCore e n (c j.1 * c j.2)
    (rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)) 0 :
      Set (rankThickening (Over.mk p) n 0)))
attribute [local irreducible] rankStageCore rankStageCompatibleOverlapError
  rankStageChosenBoundaryCoreTower rankStageGlobalBoundaryKernel
  rankStageGlobalCoreRestriction rankStageInvariantTransition

include hclosed in
/-- The actual full original-boundary overlap errors extend unscaled at every order. -/
theorem exists_rankStage_clopen_boundary_overlap_numerators :
    ∃ w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k,
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
      ∀ j k, rankStageGlobalCoreRestriction e n (a j) (ha j) k (w j k) = (x j).val k := by
  have H (j : ι × ι) := exists_rankStage_clopen_core_numerators e n (a j) (ha j)
    (hclosed j) J (x j)
    (rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t c hc j.1 j.2)
  choose w hw ht he using H
  exact ⟨w, hw, ht, he⟩

include hclosed in
/-- Clopen pairwise supports kill the exact original scalar overlap obstruction. -/
theorem rankStageOriginalBoundaryOverlapIdeal_eq_top_of_cores_closed :
    rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t c hc = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [one_mem_rankStageOriginalBoundaryOverlapIdeal]
  simpa only [rankStageCompatibleOverlapError] using
    exists_rankStage_clopen_boundary_overlap_numerators e n J hJ f hf t c hc hclosed

end FLT.Mazur.EquivalenceRelationOrderedFrames
