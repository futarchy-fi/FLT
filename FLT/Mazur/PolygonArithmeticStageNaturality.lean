/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticOriginalAdicSquare
public import FLT.Mazur.PolygonArithmeticStageProjTransition
public import FLT.Mazur.SectionRetainedProjNaturality

/-!
# Original polygon transitions under retained stage recovery

The recovery isomorphisms intertwine the original stage system maps with
the independently defined W208 retained Proj transitions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family
  SectionRetainedProjConstruction.toProj Proj.map

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) (n : ℕ) (h : 2 ≤ n)
    [NeZero n]

/-- The canonical recovery is natural for the actual original polygon stage maps. -/
@[reassoc]
theorem boundaryStageRetainedIso_naturality {a b : ℕ} (f : a ⟶ b) :
    (boundaryStageRetainedIso A π hne hgen n h a).hom ≫ boundaryVeroneseProjTransition A π hne
    hgen n h f =
      (stageSystem A π n h).map f ≫ (boundaryStageRetainedIso A π hne hgen n h b).hom := by
  let _ := boundaryExactRetainedGradedRing A π hne hgen n h a
  let _ := boundaryExactRetainedGradedRing A π hne hgen n h b
  rw [boundaryStageRetainedIso_hom, boundaryStageRetainedIso_hom]
  exact SectionRetainedProjNaturality.toProj_map ((stageSystem A π n h).map f)
    (boundaryLine A π b n h) (boundaryLine A π a n h) (boundaryLineSystemIso A π n h f)
    (exactVeroneseStep A π hne hgen n h) (boundaryExactRetainedGenerated A π hne hgen n h b)
    (boundaryExactRetainedGenerated A π hne hgen n h a) (boundaryVeroneseTransition_irrelevant A π
    hne hgen n h f)

/-- Original stage evaluations form a compatible system of morphisms into the complete Proj. -/
@[reassoc]
theorem originalStageToCompatibleProj_naturality {a b : ℕ} (f : a ⟶ b) :
    (stageSystem A π n h).map f ≫ originalStageToCompatibleProj A π hne hgen n h b =
      originalStageToCompatibleProj A π hne hgen n h a := by
  rw [originalStageToCompatibleProj, ← Category.assoc,
    ← boundaryStageRetainedIso_naturality, Category.assoc,
    boundaryVeroneseProjTransition_toCompatible]
  rfl

/-- The original polygon stage system has its actual compatible Proj cocone. -/
def originalStageCompatibleProjCocone : CategoryTheory.Limits.Cocone (stageSystem A π n h) where
  pt := exactVeroneseProj A π n h hne hgen
  ι :=
    { app := originalStageToCompatibleProj A π hne hgen n h
      naturality := by
        intro a b f
        change (stageSystem A π n h).map f ≫ originalStageToCompatibleProj A π hne hgen n h b =
          originalStageToCompatibleProj A π hne hgen n h a ≫ 𝟙 _
        rw [Category.comp_id]
        exact originalStageToCompatibleProj_naturality A π hne hgen n h f }

end FLT.Mazur.PolygonArithmeticStages
