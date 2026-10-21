/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryScalarAnnihilation

/-!
# Original full-source lift denominators control rank correction classes

A scalar multiple of the original boundary section that lifts to an original
invariant supplies an actual global rank tower, hence exact whole-core
corrections. The ideal is defined by original-source solvability, with the
full boundary retained. No converse or algebraization is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A}
  (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))

/-- Original scalars for which the exact scaled boundary has an original invariant lift. -/
def originalBoundaryLiftIdeal : Ideal (compatibleFunctions p q) where
  carrier := {s | ∃ r : compatibleFunctions p q,
    J.subschemeι.appTop r.val = J.subschemeι.appTop s.val * t}
  zero_mem' := ⟨0, by simp only [ZeroMemClass.coe_zero, map_zero, zero_mul]⟩
  add_mem' := by
    rintro s u ⟨r, hr⟩ ⟨w, hw⟩
    refine ⟨r + w, ?_⟩
    change J.subschemeι.appTop (r.val + w.val) =
      J.subschemeι.appTop (s.val + u.val) * t
    rw [map_add, map_add, hr, hw, add_mul]
  smul_mem' := by
    rintro s u ⟨r, hr⟩
    refine ⟨s * r, ?_⟩
    change J.subschemeι.appTop (s.val * r.val) =
      J.subschemeι.appTop (s.val * u.val) * t
    rw [map_mul, map_mul, hr, mul_assoc]

/-- Scalars vanishing on the full boundary lift its scaled value by zero. -/
theorem originalBoundaryScalarKernel_le_liftIdeal :
    originalBoundaryScalarKernel (p := p) (q := q) J ≤ originalBoundaryLiftIdeal J t := by
  intro s hs
  refine ⟨0, ?_⟩
  change J.subschemeι.appTop 0 = J.subschemeι.appTop s.val * t
  rw [(mem_originalBoundaryScalarKernel J s).mp hs, map_zero, zero_mul]

/-- Unit membership is exact lifting on the unchanged original source. -/
theorem one_mem_originalBoundaryLiftIdeal :
    1 ∈ originalBoundaryLiftIdeal (p := p) (q := q) J t ↔
      ∃ r : compatibleFunctions p q, J.subschemeι.appTop r.val = t := by
  change (∃ r : compatibleFunctions p q,
    J.subschemeι.appTop r.val = J.subschemeι.appTop 1 * t) ↔ _
  rw [map_one, one_mul]

variable [IsSeparated p] [Etale p] [QuasiCompact p] [Etale q]
  [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance originalLiftOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalLiftOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalLiftOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))
  (hv : ∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
    ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t)
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition rankStageCoreCorrectionIdeal
  rankStageCoreCorrectionObstruction

include hv in
/-- Original-source lift denominators annihilate the actual full rank correction class. -/
theorem originalBoundaryLiftIdeal_le_correctionIdeal :
    originalBoundaryLiftIdeal (p := p) (q := q) J t ≤
      rankStageCoreCorrectionIdeal e n c hc J v := by
  rintro s ⟨r, hr⟩
  rw [mem_rankStageCoreCorrectionIdeal_iff_scaled_class]
  apply rankStageCoreCorrectionObstruction_eq_zero_of_global e n c hc J (s • v)
    (rankStageOriginalCompatibleScalars e n r) (J.subschemeι.appTop s.val * t)
  · intro j k
    simpa only [Pi.smul_apply, sub_zero] using
      rankStageCoreCorrection_scaled_boundary e n c hc J j s (v j) 0 t
        (hv j) (fun _ ↦ map_zero _) k
  · intro k
    change (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop
      ((rankThickeningMap (Over.mk p) n k).appTop r.val) = _
    exact (IdealSheafClosedTransitions.section_square _ _ _ rfl r.val).trans
      (congrArg (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop hr)

include hv in
/-- Actual rank correction support is confined to original-source lifting failure. -/
theorem rankStageCoreCorrection_support_subset_original_lift :
    PrimeSpectrum.zeroLocus
        (rankStageCoreCorrectionIdeal e n c hc J v : Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t : Set (compatibleFunctions p q)) := by
  intro x hx
  exact (originalBoundaryLiftIdeal_le_correctionIdeal J t e n c hc v hv).trans hx

end FLT.Mazur.EquivalenceRelationOrderedFrames
