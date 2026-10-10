/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageRetainedCanonicalMap
public import FLT.Mazur.PolygonInfinitesimalStageProper
public import FLT.Mazur.ProperAmpleRetainedProjIso
public import FLT.Mazur.SectionRetainedProjStructuralMap

/-!
# Recovering the original proper polygon stages

Each retained section Proj is isomorphic to the original polygon stage via
its actual section-evaluation map. The isomorphism retains the original
truncated-polynomial base and transfers the proved flatness and properness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family
  SectionRetainedProjConstruction.toProj SectionRetainedProjStructuralMap.toBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Actual section evaluation is an isomorphism from each original polygon stage. -/
theorem boundaryStageToExactVeroneseProj_isIso (m : ℕ) :
    IsIso (boundaryStageToExactVeroneseProj K n h m) :=
  ProperAmpleRetainedProjIso.isIso (family K m n h).hom (boundaryLine K m n h)
    (exactVeroneseStep K n h) (boundaryLine_ample K m n h)
    (exactVeroneseStep_pos K n h) (boundaryExactRetainedGenerated K n h m)

/-- The recovery isomorphism uses the original scheme and the original evaluation morphism. -/
def boundaryStageRetainedIso (m : ℕ) :
    (family K m n h).left ≅ boundaryExactVeroneseProj K n h m := by
  let _ := boundaryStageToExactVeroneseProj_isIso K n h m
  exact asIso (boundaryStageToExactVeroneseProj K n h m)

/-- Stage recovery retains its independently constructed canonical evaluation map. -/
theorem boundaryStageRetainedIso_hom (m : ℕ) :
    (boundaryStageRetainedIso K n h m).hom = boundaryStageToExactVeroneseProj K n h m := rfl

/-- The retained Proj's structural map to the original truncated-polynomial base. -/
def boundaryRetainedProjToOriginalBase (m : ℕ) :
    boundaryExactVeroneseProj K n h m ⟶ Spec (.of (Ring K m)) :=
  SectionRetainedProjStructuralMap.toBase (boundaryLine K m n h)
    (exactVeroneseStep K n h) (family K m n h).hom

/-- Recovery retains the actual original stage structure morphism. -/
@[reassoc]
theorem boundaryStageRetainedIso_toOriginalBase (m : ℕ) :
    (boundaryStageRetainedIso K n h m).hom ≫ boundaryRetainedProjToOriginalBase K n h m =
      (family K m n h).hom :=
  SectionRetainedProjStructuralMap.toProj_toBase (boundaryLine K m n h)
    (exactVeroneseStep K n h) (family K m n h).hom (boundaryExactRetainedGenerated K n h m)

/-- The inverse recovery map also preserves the original base morphism. -/
@[reassoc]
theorem boundaryStageRetainedIso_inv_toOriginalBase (m : ℕ) :
    (boundaryStageRetainedIso K n h m).inv ≫ (family K m n h).hom =
      boundaryRetainedProjToOriginalBase K n h m := by
  rw [← boundaryStageRetainedIso_toOriginalBase K n h m, Iso.inv_hom_id_assoc]

/-- The recovered stage Proj retains the proved flatness of the original infinitesimal family. -/
theorem boundaryRetainedProjToOriginalBase_flat (m : ℕ) :
    Flat (boundaryRetainedProjToOriginalBase K n h m) := by
  rw [← boundaryStageRetainedIso_inv_toOriginalBase K n h m]
  infer_instance

/-- The recovered stage Proj retains the proved properness of the original infinitesimal family. -/
theorem boundaryRetainedProjToOriginalBase_proper (m : ℕ) :
    IsProper (boundaryRetainedProjToOriginalBase K n h m) := by
  rw [← boundaryStageRetainedIso_inv_toOriginalBase K n h m]
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
