/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameCompleteFinite
public import FLT.Mazur.EquivalenceRelationCompleteClosedLocus

/-!
# Whole original relation finiteness on complete normalized tests

The complete-support condition splits the original first projection after
base change to an arbitrary test. No finiteness of just a selected relation
or of the moving permutation action is substituted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I) {T : Scheme} (j : T ⟶ source p q I o)
local instance completeTestFinite_overEtale : Etale (Over.mk p).hom := ‹Etale p›
local instance completeTestFinite_overSeparated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
attribute [local irreducible] source distinctScheme completeLocus

/-- Complete normalized support makes the whole original pulled projection finite. -/
theorem original_pullback_finite_of_complete
    (hj : Set.range j ⊆ completePointLocus (p := p) (q := q) I o) :
    IsFinite (pullback.snd p (j ≫ first p q I o)) := by
  let t : Over.mk (j ≫ first p q I o) ⟶ distinctScheme (Over.mk p) I :=
    Over.homMk (j ≫ inclusion p q I o) (Category.assoc _ _ _)
  apply finite_pullback_of_complete (Over.mk p) I t
  rintro _ ⟨x, rfl⟩
  have hx := hj (Set.mem_range_self x)
  rw [completePointLocus_eq_preimage] at hx
  exact hx

end FLT.Mazur.EquivalenceRelationNormalizedFrames
