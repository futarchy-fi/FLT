/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteInterior
public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts
public import FLT.Mazur.GeometricPointCoverCriterion
public import FLT.Mazur.RelativeTupleFiniteCompleteness
public import FLT.Mazur.SchemeFiniteTargetBaseChange

/-!
# Complete normalized frames over the original finite target locus

An actual finite neighborhood of the original first projection makes every
complete normalized lift an interior complete point. No finiteness of the
restricted moving action or of just the enumerated sections is substituted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I)

local instance finiteCompleteOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteCompleteOver_etale : Etale (Over.mk p).hom := ‹Etale p›

/-- Pull back the constructed finite complete open along the actual frame inclusion. -/
def finiteCompleteFrameOpen : (source p q I o).Opens :=
  inclusion p q I o ⁻¹ᵁ finiteCompleteOpen (Over.mk p) I

/-- Every point of this genuine open is complete for the full original relation. -/
theorem finiteCompleteFrameOpen_le_interior :
    finiteCompleteFrameOpen (p := p) (q := q) I o ≤ completeInterior I o := by
  apply le_completeInterior
  intro x hx
  rw [completePointLocus_eq_preimage]
  exact finiteCompleteOpen_subset (Over.mk p) I hx

/-- A complete frame over an actual finite original neighborhood lies in the constructed open. -/
theorem mem_finiteCompleteFrameOpen (x : source p q I o)
    (hc : x ∈ completePointLocus (p := p) (q := q) I o)
    (hf : first p q I o x ∈ finiteTargetOpen p) :
    x ∈ finiteCompleteFrameOpen (p := p) (q := q) I o := by
  apply (mem_finiteCompleteOpen (Over.mk p) I (inclusion p q I o x)).mpr
  refine ⟨?_, ?_⟩
  · exact preimage_finiteTargetOpen_le
      (IsPullback.of_hasPullback p (distinctScheme (Over.mk p) I).hom) hf
  · rw [completePointLocus_eq_preimage] at hc
    exact hc

/-- Finiteness near the original endpoint removes the complete-interior obstruction. -/
theorem complete_mem_interior_of_finiteTarget (x : source p q I o)
    (hc : x ∈ completePointLocus (p := p) (q := q) I o)
    (hf : first p q I o x ∈ finiteTargetOpen p) :
    x ∈ completeInterior (p := p) (q := q) I o :=
  finiteCompleteFrameOpen_le_interior I o (mem_finiteCompleteFrameOpen I o x hc hf)

/-- With a finite original first projection, all complete normalized points are interior. -/
theorem complete_mem_interior_of_finite [IsFinite p] (x : source p q I o)
    (hc : x ∈ completePointLocus (p := p) (q := q) I o) :
    x ∈ completeInterior (p := p) (q := q) I o := by
  apply complete_mem_interior_of_finiteTarget I o x hc
  rw [finiteTargetOpen_eq_top]
  trivial

variable [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Every original point has a complete normalized lift, including its intrinsic completeness. -/
theorem exists_complete_normalized_point (x : A) :
    ∃ (n : ℕ) (o : Fin n) (y : source p q (Fin n) o),
      first p q (Fin n) o y = x ∧ y ∈ completePointLocus (p := p) (q := q) (Fin n) o := by
  let K := AlgebraicClosure (A.residueField x)
  let g : Spec (.of K) ⟶ Spec (A.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (A.residueField x) K))
  obtain ⟨n, o, u, hu, hc⟩ := exists_complete_normalized_lift e (g ≫ A.fromSpecResidueField x)
  refine ⟨n, o, u default, ?_, (complete_iff_mem_completePointLocus _ _ u).mp hc⟩
  change (u ≫ first p q (Fin n) o) default = x
  rw [hu, Scheme.Hom.comp_apply]
  exact A.fromSpecResidueField_apply x _

include e in
/-- Actual finite original neighborhoods supply interior complete lifts at every point. -/
theorem exists_complete_interior_lift_of_finiteTarget (x : A)
    (hx : x ∈ finiteTargetOpen p) :
    ∃ (n : ℕ) (o : Fin n) (y : source p q (Fin n) o),
      first p q (Fin n) o y = x ∧ y ∈ completeInterior (p := p) (q := q) (Fin n) o := by
  obtain ⟨n, o, y, hy, hc⟩ := exists_complete_normalized_point e x
  exact ⟨n, o, y, hy, complete_mem_interior_of_finiteTarget (Fin n) o y hc (by rwa [hy])⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
