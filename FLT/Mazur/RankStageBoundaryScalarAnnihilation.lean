/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousCochainAnnihilation
public import FLT.Mazur.RankStageBoundaryCorrectionClass
public import FLT.Mazur.RankStageCoreCorrectionSupport

/-!
# Full boundary scalars annihilate actual compatible correction classes

The contraction of the unchanged full boundary ideal annihilates every
core correction class. The correction is the scaled whole cochain itself,
so no affineness, stationary powers, or finite correction cokernel is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

variable {D A : Scheme.{0}} {p q : D ⟶ A}

/-- Original invariant scalars vanishing on the full unchanged boundary. -/
def originalBoundaryScalarKernel (J : A.IdealSheafData) : Ideal (compatibleFunctions p q) :=
  RingHom.ker (J.subschemeι.appTop.hom.comp (compatibleFunctions p q).subtype)

/-- Kernel membership retains the full boundary equation, including nilpotents. -/
theorem mem_originalBoundaryScalarKernel (J : A.IdealSheafData) (s : compatibleFunctions p q) :
    s ∈ originalBoundaryScalarKernel (p := p) (q := q) J ↔ J.subschemeι.appTop s.val = 0 :=
  Iff.rfl

variable [IsSeparated p] [Etale p] [QuasiCompact p] [Etale q]
  [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryAnnihilationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryAnnihilationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryAnnihilationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n) (J : A.IdealSheafData)
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition rankStageCoreCorrectionIdeal
  rankStageCompatibleCoreRefinement

/-- A boundary-vanishing original scalar makes any whole core tower homogeneous. -/
theorem rankStageCore_smul_boundary_zero (j : ι) (s : compatibleFunctions p q)
    (hs : s ∈ originalBoundaryScalarKernel (p := p) (q := q) J)
    (v : rankStageCompatibleCoreInvariants e n (c j) (hc j)) (k : ℕ) :
    (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
      ((s • v).val k).val = 0 := by
  rw [rankStageOriginalCore_smul_val e n c hc, map_mul]
  have hsq := IdealSheafClosedTransitions.section_square _ _ _
    (rankStageCoreOriginalMap_ideal e n (c j) (hc j) J k) s.val
  rw [(mem_originalBoundaryScalarKernel J s).mp hs, map_zero] at hsq
  rw [hsq, zero_mul]

/-- The full original boundary kernel lies in every actual cochain correction ideal. -/
theorem originalBoundaryScalarKernel_le_correctionIdeal
    (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)) :
    originalBoundaryScalarKernel (p := p) (q := q) J ≤
      rankStageCoreCorrectionIdeal e n c hc J v := by
  intro s hs
  unfold rankStageCoreCorrectionIdeal
  apply HomogeneousCochainCorrection.mem_scalarIdeal_of_smul_mem
  intro j k
  exact rankStageCore_smul_boundary_zero e n c hc J j s hs (v j) k

/-- The genuine class is supported on the full contracted original boundary locus. -/
theorem rankStageCoreCorrection_support_subset_boundary
    (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)) :
    PrimeSpectrum.zeroLocus
        (rankStageCoreCorrectionIdeal e n c hc J v : Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus
        (originalBoundaryScalarKernel (p := p) (q := q) J : Set (compatibleFunctions p q)) := by
  intro x hx
  exact (originalBoundaryScalarKernel_le_correctionIdeal e n c hc J v).trans hx

end FLT.Mazur.EquivalenceRelationOrderedFrames
