/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompletePointLocus
public import FLT.Mazur.RelativeGeometricFrameLocus

/-!
# The intrinsic normalized complete locus is closed

The set defined by residue-field completeness is the inverse image of the actual
residual-scheme completeness locus. This identifies its geometry and proves it
closed and saturated under the original relation. No open neighborhood follows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I)

local instance closedLocusOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance closedLocusOver_etale : Etale (Over.mk p).hom := ‹Etale p›

/-- Geometric completeness is exactly membership in the original closed tuple locus. -/
theorem complete_iff_mem_tupleLocus {K : Type} [Field K]
    (u : Spec (.of K) ⟶ source p q I o) :
    Complete I o u ↔ inclusion p q I o (u default) ∈ completeLocus (Over.mk p) I := by
  have h := geometric_complete_iff_mem_completeLocus (Over.mk p) I (testFrame I o u)
  exact h

/-- The intrinsic normalized complete set is an actual inverse image of the residual locus. -/
theorem completePointLocus_eq_preimage :
    completePointLocus (p := p) (q := q) I o =
      inclusion p q I o ⁻¹' completeLocus (Over.mk p) I := by
  ext x
  have h := complete_iff_mem_tupleLocus I o ((source p q I o).fromSpecResidueField x)
  have hx : (source p q I o).fromSpecResidueField x default = x :=
    Scheme.fromSpecResidueField_apply x default
  exact h.trans (congrArg (fun y ↦ inclusion p q I o y ∈ completeLocus (Over.mk p) I)
    hx).to_iff

/-- Complete normalized points form a closed set, without any openness assertion. -/
theorem completePointLocus_isClosed :
    IsClosed (completePointLocus (p := p) (q := q) I o) := by
  rw [completePointLocus_eq_preimage]
  exact (completeLocus_isClosed (Over.mk p) I).preimage (inclusion p q I o).continuous

/-- Incompleteness is the inverse image of the existing residual projection's open image. -/
theorem incompletePointLocus_eq_preimage :
    (completePointLocus (p := p) (q := q) I o)ᶜ =
      inclusion p q I o ⁻¹' (incompleteOpen (Over.mk p) I : Set _) := by
  simp only [completePointLocus_eq_preimage, completeLocus, Set.preimage_compl, compl_compl]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
