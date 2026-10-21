/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFiniteOriginalNorm
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# Common original norm annihilators for arbitrary finite chart families

A product of norms in the unchanged original invariant ring annihilates
all selected full homogeneous errors. Original chart parameters may be
arbitrary; finiteness of the original relation constructs all required
rank stabilization. Only the finite family index is combined.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections FiniteFlatRelationNormCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] [IsFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance normProductOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance normProductOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance normProductOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]
  {ι : Type*} [Fintype ι] (n : ι → ℕ)
  (a : ι → Γ(A, ⊤))
  (hs : ∀ j, A.basicOpen (a j) ≤ rankImageOpen (Over.mk p) (n j))
  (J : A.IdealSheafData)
  (x : ∀ j, rankStageCompatibleCoreInvariants e (n j) (a j) (hs j))
  (hx : ∀ j k, (rankStageCoreBoundaryIdeal e (n j) (a j) (hs j) J k).subschemeι.appTop
    ((x j).val k).val = 0)
attribute [local irreducible] rankStageCore rankStageOriginalNumeratorIdeal
  rankStageCompatibleNumeratorIdeal rankStageOriginalCompatibleScalars

include hf hx in
/-- A constructed product in the unchanged scalar ring kills every full selected obstruction. -/
theorem rankStageOriginalNormProduct_mem_radical :
    (∏ j, rankStageOriginalNorm e (a j)) ∈
      (rankStageFamilyNumeratorIdeal e n a hs J x).radical := by
  classical
  apply (FiniteScalarObstruction.mem_radical_jointIdeal _ _).mpr
  intro j
  have hj := rankStageOriginalNorm_mem_radical_of_finite e (n j) (a j) (hs j)
    J (x j) f hf (hx j)
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem
    (fun j ↦ rankStageOriginalNorm e (a j)) (Finset.mem_univ j)
  rw [hb]
  exact Ideal.mul_mem_right _ _ hj

include hf hx in
/-- One exponent in the original ring gives ordinary compatible full homogeneous numerators. -/
theorem exists_rankStageOriginalNormProduct_uniform :
    ∃ (N : ℕ) (w : ∀ j k, rankStageInvariants e (n j) k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e (n j) J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e (n j) h (w j l) = w j k) ∧
      ∀ j k, rankStageGlobalCoreRestriction e (n j) (a j) (hs j) k (w j k) =
        (rankStageGlobalCoreRestriction e (n j) (a j) (hs j) k
          (rankStageOriginalInvariantRestriction e (n j) k
            (∏ j, rankStageOriginalNorm e (a j)))) ^ N *
            (x j).val k := by
  apply exists_rankStage_family_uniform_numerators e n a hs J x (∏ j, rankStageOriginalNorm e (a j))
  exact (FiniteScalarObstruction.mem_radical_jointIdeal _ _).mp
    (rankStageOriginalNormProduct_mem_radical e f hf n a hs J x hx)

end FLT.Mazur.EquivalenceRelationOrderedFrames
