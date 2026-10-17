/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteInteriorFinite

/-!
# Actual residual arrows near every frame over a nonfinite target point

Every open neighborhood of such a frame contains a point with an unenumerated
arrow in the whole original pullback. Even a complete central frame cannot
avoid this residual obstruction by choosing a smaller open neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) [LocallyQuasiFinite p]
  (I : Type) [Fintype I] (o : I)
local instance nonfiniteResidual_overEtale : Etale (Over.mk p).hom := ‹Etale p›
local instance nonfiniteResidual_overSeparated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
attribute [local irreducible] source first distinctScheme

include e in
/-- Nonfinite original points force an actual missing arrow in every frame neighborhood. -/
theorem exists_residual_in_every_neighborhood (x : source p q I o)
    (hx : first p q I o x ∉ finiteTargetOpen p)
    (U : (source p q I o).Opens) (hxU : x ∈ U) :
    ∃ (y : source p q I o), y ∈ U ∧
      ∃ z : framedSource (Over.mk p) I,
        framedProjection (Over.mk p) I z = inclusion p q I o y ∧
          z ∉ enumeratedOpen (Over.mk p) I := by
  classical
  have hn : ¬ ∀ y ∈ U, y ∈ completePointLocus (p := p) (q := q) I o := by
    intro h
    exact hx (completeInterior_le_finiteTarget e I o (le_completeInterior I o U h hxU))
  push Not at hn
  obtain ⟨y, hyU, hy⟩ := hn
  have hb : y ∈ (completePointLocus (p := p) (q := q) I o)ᶜ := hy
  rw [incompletePointLocus_eq_preimage] at hb
  obtain ⟨z, hz⟩ := hb
  exact ⟨y, hyU, z.val, hz, z.property⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
