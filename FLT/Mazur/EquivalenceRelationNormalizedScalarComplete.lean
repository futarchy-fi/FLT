/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedCompleteRelation
public import FLT.Mazur.RelativeFrameScalarCompleteness

/-!
# Normalized completeness is invariant under scalar extension

This applies to the original normalized source and its actual test frames.
No restriction of the original relation or of its independent endpoints occurs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (I : Type) [Fintype I] (o : I)

local instance scalarOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local notation "E" => Over.mk p
variable {K L : Type} [Field K] [Field L] (u : Spec (.of K) ⟶ source p q I o)
  (g : Spec (.of L) ⟶ Spec (.of K))

omit [Etale p] in
/-- The scalar-extended normalized frame is the original pulled tuple, with its base cast. -/
theorem testFrame_scalar :
    testFrame I o (g ≫ u) = frameCast I (Category.assoc g u (first p q I o)).symm
      (scalarFrame E I (testFrame I o u) g) := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

/-- Complete normalized frames stay complete over all field extensions. -/
theorem complete_scalar (hu : Complete I o u) : Complete I o (g ≫ u) := by
  unfold Complete
  rw [testFrame_scalar]
  exact frameCast_complete I _ _ (scalarFrame_complete E I (testFrame I o u) g hu)

/-- Scalar extension both preserves and detects normalized completeness. -/
theorem complete_scalar_iff : Complete I o (g ≫ u) ↔ Complete I o u := by
  refine ⟨fun h ↦ ?_, complete_scalar I o u g⟩
  have hc := frameCast_complete I (Category.assoc g u (first p q I o))
    (testFrame I o (g ≫ u)) h
  have he : frameCast I (Category.assoc g u (first p q I o))
      (testFrame I o (g ≫ u)) = scalarFrame E I (testFrame I o u) g := by
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _
  rw [he] at hc
  exact (scalarFrame_complete_iff E I (testFrame I o u) g).mp hc

end FLT.Mazur.EquivalenceRelationNormalizedFrames
