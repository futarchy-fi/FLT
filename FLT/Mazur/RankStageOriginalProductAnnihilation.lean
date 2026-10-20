/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageClopenKernelObstruction
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# One constructed original scalar for a finite family of full rank obstructions

For invariant original principal parameters, the product of the parameters
belongs to every all-order obstruction radical. The finite intersection
therefore has one actual original-scalar annihilator; no norm descent or
interchange with the infinite order index is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance productScalarOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance productScalarOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance productScalarOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]
  {ι : Type*} [Fintype ι] (n : ι → ℕ)
  (hn : ∀ j, IsClosed (rankImageOpen (Over.mk p) (n j + 1) : Set A))
  (s : ι → compatibleFunctions p q)
  (hs : ∀ j, A.basicOpen (s j).val ≤ rankImageOpen (Over.mk p) (n j))
  (J : A.IdealSheafData)
  (x : ∀ j, rankStageCompatibleCoreInvariants e (n j) (s j).val (hs j))
  (hx : ∀ j k, (rankStageCoreBoundaryIdeal e (n j) (s j).val (hs j) J k).subschemeι.appTop
    ((x j).val k).val = 0)
attribute [local irreducible] rankStageCore rankStageOriginalNumeratorIdeal
  rankStageCompatibleNumeratorIdeal rankStageOriginalCompatibleScalars

include hn hf hx in
/-- A constructed product in the unchanged scalar ring kills every full selected obstruction. -/
theorem rankStageOriginalProduct_mem_radical :
    (∏ j, s j) ∈
      (rankStageFamilyNumeratorIdeal e n (fun j ↦ (s j).val) hs J x).radical := by
  classical
  apply (FiniteScalarObstruction.mem_radical_jointIdeal _ _).mpr
  intro j
  have hj := rankStageOriginalScalar_mem_radical_of_next_closed e (n j) (hn j)
    J f hf (s j) (hs j) (x j) (hx j)
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ j)
  rw [hb]
  exact Ideal.mul_mem_right _ _ hj

include hn hf hx in
/-- One exponent in the original ring gives ordinary compatible full homogeneous numerators. -/
theorem exists_rankStageOriginalProduct_uniform :
    ∃ (N : ℕ) (w : ∀ j k, rankStageInvariants e (n j) k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e (n j) J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e (n j) h (w j l) = w j k) ∧
      ∀ j k, rankStageGlobalCoreRestriction e (n j) (s j).val (hs j) k (w j k) =
        (rankStageGlobalCoreRestriction e (n j) (s j).val (hs j) k
          (rankStageOriginalInvariantRestriction e (n j) k (∏ j, s j))) ^ N * (x j).val k := by
  apply exists_rankStage_family_uniform_numerators e n (fun j ↦ (s j).val) hs J x (∏ j, s j)
  exact (FiniteScalarObstruction.mem_radical_jointIdeal _ _).mp
    (rankStageOriginalProduct_mem_radical e f hf n hn s hs J x hx)

end FLT.Mazur.EquivalenceRelationOrderedFrames
