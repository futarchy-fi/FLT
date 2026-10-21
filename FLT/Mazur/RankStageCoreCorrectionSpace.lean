/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreCorrectionCokernel

/-!
# A named carrier for the full rank-core correction class

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
local instance correctionSpaceOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance correctionSpaceOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance correctionSpaceOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
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

/-- A named carrier keeps quotient instances out of expanded equality types. -/
def rankStageCoreCorrectionSpace : Type _ :=
  (∀ i j, O i j) ⧸ rankStageCoreCorrectionImage e n c hc J

noncomputable instance rankStageCoreCorrectionSpaceAddCommGroup :
    AddCommGroup (rankStageCoreCorrectionSpace e n c hc J) :=
  inferInstanceAs (AddCommGroup ((∀ i j, O i j) ⧸ rankStageCoreCorrectionImage e n c hc J))

noncomputable instance rankStageCoreCorrectionSpaceModule :
    Module (compatibleFunctions p q) (rankStageCoreCorrectionSpace e n c hc J) :=
  inferInstanceAs (Module (compatibleFunctions p q)
    ((∀ i j, O i j) ⧸ rankStageCoreCorrectionImage e n c hc J))

/-- The genuine full homogeneous correction class in its named carrier. -/
noncomputable def rankStageCoreCorrectionObstruction (v : ∀ j, C j) :
    rankStageCoreCorrectionSpace e n c hc J :=
  rankStageCoreCorrectionClass e n c hc J v

/-- The unit belongs to the scalar ideal precisely when the full class vanishes. -/
theorem one_mem_rankStageCoreCorrectionIdeal (v : ∀ j, C j) :
    1 ∈ rankStageCoreCorrectionIdeal e n c hc J v ↔
      rankStageCoreCorrectionObstruction e n c hc J v = 0 := by
  unfold rankStageCoreCorrectionIdeal rankStageCoreCorrectionObstruction
    rankStageCoreCorrectionClass
  exact HomogeneousCochainCorrection.one_mem_scalarIdeal L R K v

end FLT.Mazur.EquivalenceRelationOrderedFrames
