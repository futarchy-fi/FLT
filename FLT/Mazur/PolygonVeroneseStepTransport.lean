/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPositiveRetainedStage
public import FLT.Mazur.PolygonMultipleVeroneseStructuralMap

/-!
# Equality transport for compatible retained steps

Equal numerical steps give the same original model, structural map and stage
maps. This handles product commutativity without identifying independent choices.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] originalStageToMultipleProj
variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q t : ℕ) (e : q = t)

/-- Numerical equality transports the original compatible projective spectrum. -/
def veroneseStepIso :
    Proj (compatibleVeroneseGrade R n h q) ≅ Proj (compatibleVeroneseGrade R n h t) :=
  eqToIso (congrArg (fun a ↦ Proj (compatibleVeroneseGrade R n h a)) e)

/-- Equality transport leaves the original complete structural map unchanged. -/
@[reassoc]
theorem veroneseStepIso_toBase :
    (veroneseStepIso R n h q t e).hom ≫
      GradedProjStructuralMap.toSpecBase (compatibleVeroneseGrade R n h t) =
        GradedProjStructuralMap.toSpecBase (compatibleVeroneseGrade R n h q) := by
  subst t
  simp only [veroneseStepIso, eqToIso_refl, Iso.refl_hom, Category.id_comp]

variable (K : Type) [Field K] [NeZero n] [NeZero q] [NeZero t]

/-- Equality transport retains the actual original stage map at an exact multiple. -/
@[reassoc]
theorem originalStageToMultipleProj_stepIso
    (hq : exactVeroneseStep K n h ∣ q) (ht : exactVeroneseStep K n h ∣ t) (m : ℕ) :
    originalStageToMultipleProj K n h q hq m ≫ (veroneseStepIso K n h q t e).hom =
      originalStageToMultipleProj K n h t ht m := by
  subst t
  simp only [veroneseStepIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
