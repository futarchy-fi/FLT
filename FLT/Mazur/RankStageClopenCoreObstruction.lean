/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageClopenCoreExtension
public import FLT.Mazur.RankStageOriginalCompatibleScalars

/-!
# Vanishing of the full compatible obstruction on clopen rank cores

Extension by zero constructs unscaled ordinary compatible homogeneous
numerators at every order. Both the compatible and unchanged original-scalar
numerator ideals are the unit ideal. No stationarity of rank powers is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance clopenObstructionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance clopenObstructionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance clopenObstructionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (hclosed : IsClosed (rankStageCore e n a ha 0 : Set (rankThickening (Over.mk p) n 0)))
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)
attribute [local irreducible] rankStageCore rankStageInvariantTransition
  rankStageGlobalCoreRestriction rankStageGlobalBoundaryKernel
  rankStageCompatibleNumeratorIdeal rankStageClopenCoreExtension

include hclosed hx in
/-- A clopen support gives exact compatible homogeneous numerators with multiplier one. -/
theorem exists_rankStage_clopen_core_numerators :
    ∃ w : ∀ k, rankStageInvariants e n k,
      (∀ k, w k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
      ∀ k, rankStageGlobalCoreRestriction e n a ha k (w k) = x.val k := by
  refine ⟨fun k ↦ rankStageClopenCoreExtension e n a ha hclosed k (x.val k),
    fun k ↦ rankStageClopenCoreExtension_boundary e n a ha hclosed J k (x.val k) (hx k),
    ?_, fun k ↦ rankStageClopenCoreExtension_restrict e n a ha hclosed k (x.val k)⟩
  intro k l h
  rw [rankStageClopenCoreExtension_transition, x.property k l h]

include hclosed hx in
/-- The full all-order compatible numerator ideal is the unit ideal on a clopen core. -/
theorem rankStageCompatibleNumeratorIdeal_eq_top_of_core_closed :
    rankStageCompatibleNumeratorIdeal e n a ha J x = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [mem_rankStageCompatibleNumeratorIdeal]
  obtain ⟨w, hw, ht, he⟩ := exists_rankStage_clopen_core_numerators e n a ha hclosed J x hx
  refine ⟨w, hw, ht, fun k ↦ ?_⟩
  simpa only [OneMemClass.coe_one, Pi.one_apply, map_one, one_mul] using he k

include hclosed hx in
/-- The unchanged original-scalar obstruction also vanishes, with no replacement norm. -/
theorem rankStageOriginalNumeratorIdeal_eq_top_of_core_closed :
    rankStageOriginalNumeratorIdeal e n a ha J x = ⊤ := by
  unfold rankStageOriginalNumeratorIdeal
  rw [rankStageCompatibleNumeratorIdeal_eq_top_of_core_closed e n a ha hclosed J x hx]
  exact Ideal.comap_top

end FLT.Mazur.EquivalenceRelationOrderedFrames
