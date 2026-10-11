/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleVeroneseProj
public import FLT.Mazur.PolygonStageRetainedRecovery

/-!
# Original polygon stages at arbitrary positive retained steps

Every positive retained section Proj recovers the original proper stage.
This permits comparison of different retained steps through the actual stage,
with its original structural morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryLine family
  SectionRetainedProjConstruction.toProj SectionRetainedProjStructuralMap.toBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (q : ℕ) [NeZero q]

/-- The actual stage subring is graded at every positive step. -/
local instance positiveStageGradedRing (m : ℕ) : GradedRing (boundaryVeroneseGrade K n h q m) :=
  boundaryVeroneseGradedRing K n h q (NeZero.pos q) m

/-- The original retained presentation uses the same positive-step grading. -/
local instance positiveStageRetainedGradedRing (m : ℕ) :
    GradedRing (RetainedSubringGrading.grade
      (SectionGradedSum.grade (boundaryLine K m n h) ⊤) q) :=
  boundaryVeroneseGradedRing K n h q (NeZero.pos q) m

/-- The original boundary sections generate at every positive retained step. -/
theorem boundaryPositiveRetainedGenerated (m : ℕ) :
    SectionRetainedProjConstruction.PositivePowerGenerated (boundaryLine K m n h) q :=
  SectionRetainedProjConstruction.positivePowerGenerated_of_ample _ _
    (boundaryLine_ample K m n h) (NeZero.pos q)

/-- The actual stage is recovered by canonical section evaluation at any positive step. -/
def boundaryPositiveRetainedIso (m : ℕ) :
    (family K m n h).left ≅ Proj (boundaryVeroneseGrade K n h q m) :=
  ProperAmpleRetainedProjIso.iso (family K m n h).hom (boundaryLine K m n h) q
    (boundaryLine_ample K m n h) (NeZero.pos q) (boundaryPositiveRetainedGenerated K n h q m)

/-- The recovery uses actual sections rather than an arbitrary scheme isomorphism. -/
theorem boundaryPositiveRetainedIso_hom (m : ℕ) :
    (boundaryPositiveRetainedIso K n h q m).hom =
      SectionRetainedProjConstruction.toProj (boundaryLine K m n h) q
        (boundaryPositiveRetainedGenerated K n h q m) := rfl

/-- The retained model has the original truncated-polynomial coefficient base. -/
def boundaryPositiveRetainedToBase (m : ℕ) :
    Proj (boundaryVeroneseGrade K n h q m) ⟶ Spec (.of (Ring K m)) :=
  SectionRetainedProjStructuralMap.toBase (boundaryLine K m n h) q (family K m n h).hom

/-- Every positive-step recovery retains the actual original structural map. -/
@[reassoc]
theorem boundaryPositiveRetainedIso_toBase (m : ℕ) :
    (boundaryPositiveRetainedIso K n h q m).hom ≫ boundaryPositiveRetainedToBase K n h q m =
      (family K m n h).hom :=
  SectionRetainedProjStructuralMap.toProj_toBase (boundaryLine K m n h) q
    (family K m n h).hom (boundaryPositiveRetainedGenerated K n h q m)

variable [NeZero n]

/-- Original finite schemes map into the compatible Proj at every positive multiple. -/
def originalStageToMultipleProj (hq : exactVeroneseStep K n h ∣ q) (m : ℕ) :
    (family K m n h).left ⟶ Proj (compatibleVeroneseGrade K n h q) :=
  (boundaryPositiveRetainedIso K n h q m).hom ≫
    multipleVeroneseProjToCompatible K n h q hq m

end FLT.Mazur.PolygonInfinitesimalStages
