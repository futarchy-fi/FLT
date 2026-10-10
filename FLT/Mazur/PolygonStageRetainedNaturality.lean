/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalStageAdicSquare
public import FLT.Mazur.PolygonStageVeroneseProjTransition
public import FLT.Mazur.SectionRetainedProjNaturality

/-!
# Original polygon transitions under retained stage recovery

The recovery isomorphisms intertwine the original stage system maps with
the independently defined W208 retained Proj transitions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family
  SectionRetainedProjConstruction.toProj Proj.map

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The canonical recovery is natural for the actual original polygon stage maps. -/
@[reassoc]
theorem boundaryStageRetainedIso_naturality {a b : ℕ} (f : a ⟶ b) :
    (boundaryStageRetainedIso K n h a).hom ≫ boundaryVeroneseProjTransition K n h f =
      (stageSystem K n h).map f ≫ (boundaryStageRetainedIso K n h b).hom := by
  let _ := boundaryExactRetainedGradedRing K n h a
  let _ := boundaryExactRetainedGradedRing K n h b
  rw [boundaryStageRetainedIso_hom, boundaryStageRetainedIso_hom]
  exact SectionRetainedProjNaturality.toProj_map ((stageSystem K n h).map f)
    (boundaryLine K b n h) (boundaryLine K a n h) (boundaryLineSystemIso K n h f)
    (exactVeroneseStep K n h) (boundaryExactRetainedGenerated K n h b)
    (boundaryExactRetainedGenerated K n h a) (boundaryVeroneseTransition_irrelevant K n h f)

/-- Original stage evaluations form a compatible system of morphisms into the complete Proj. -/
@[reassoc]
theorem originalStageToCompatibleProj_naturality {a b : ℕ} (f : a ⟶ b) :
    (stageSystem K n h).map f ≫ originalStageToCompatibleProj K n h b =
      originalStageToCompatibleProj K n h a := by
  rw [originalStageToCompatibleProj, ← Category.assoc,
    ← boundaryStageRetainedIso_naturality, Category.assoc,
    boundaryVeroneseProjTransition_toCompatible]
  rfl

/-- The original polygon stage system has its actual compatible Proj cocone. -/
def originalStageCompatibleProjCocone : CategoryTheory.Limits.Cocone (stageSystem K n h) where
  pt := exactVeroneseProj K n h
  ι :=
    { app := originalStageToCompatibleProj K n h
      naturality := by
        intro a b f
        change (stageSystem K n h).map f ≫ originalStageToCompatibleProj K n h b =
          originalStageToCompatibleProj K n h a ≫ 𝟙 _
        rw [Category.comp_id]
        exact originalStageToCompatibleProj_naturality K n h f }

end FLT.Mazur.PolygonInfinitesimalStages
