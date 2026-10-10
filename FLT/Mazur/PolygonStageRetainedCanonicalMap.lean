/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageVeroneseProj
public import FLT.Mazur.PolygonInfinitesimalStageAmple
public import FLT.Mazur.SectionRetainedProjOfAmple

/-!
# Original polygon stages embed in their retained section Proj

The actual ample boundary line constructs a canonical open immersion from
each original polygon stage. Its chart formula uses the original retained
sections, and its basic-open inverse images are their original generator opens.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family
  SectionRetainedProjConstruction.toProj SectionRetainedChartMorphism.toProjOn

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage grading also supplies the generic retained-grading presentation. -/
instance boundaryExactRetainedGradedRing (m : ℕ) :
    GradedRing (RetainedSubringGrading.grade
      (SectionGradedSum.grade (boundaryLine K m n h) ⊤) (exactVeroneseStep K n h)) :=
  boundaryExactVeroneseGradedRing K n h m

/-- The original ample boundary line generates in the previously constructed exact retained step. -/
theorem boundaryExactRetainedGenerated (m : ℕ) :
    SectionRetainedProjConstruction.PositivePowerGenerated
      (boundaryLine K m n h) (exactVeroneseStep K n h) :=
  SectionRetainedProjConstruction.positivePowerGenerated_of_ample _ _
    (boundaryLine_ample K m n h) (exactVeroneseStep_pos K n h)

/-- The actual original polygon stage maps to its independently defined retained section Proj. -/
def boundaryStageToExactVeroneseProj (m : ℕ) :
    (family K m n h).left ⟶ boundaryExactVeroneseProj K n h m :=
  SectionRetainedProjConstruction.toProj (boundaryLine K m n h)
    (exactVeroneseStep K n h) (boundaryExactRetainedGenerated K n h m)

/-- The constructed stage map is an open immersion of the original polygon scheme. -/
theorem boundaryStageToExactVeroneseProj_isOpenImmersion (m : ℕ) :
    IsOpenImmersion (boundaryStageToExactVeroneseProj K n h m) :=
  SectionRetainedProjOfAmple.isOpenImmersion (boundaryLine K m n h) _
    (exactVeroneseStep_pos K n h) (boundaryLine_ample K m n h)
    (boundaryExactRetainedGenerated K n h m)

/-- Original retained-section generator charts carry the actual intrinsic fraction comparison. -/
theorem boundaryStageToExactVeroneseProj_generator (m d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d), ⊤))
    (U : (family K m n h).left.Opens)
    (hU : U ≤ sectionGeneratorOpen
      (tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d)) s) :
    U.ι ≫ boundaryStageToExactVeroneseProj K n h m =
      SectionRetainedChartMorphism.toProjOn (boundaryLine K m n h)
        (exactVeroneseStep K n h) d s hd U hU :=
  (SectionRetainedChartMorphism.toProjOn_eq _ _ _ _ hd
    (boundaryExactRetainedGenerated K n h m) U hU).symm

/-- Every original positive retained section has its exact original generator-open inverse image. -/
theorem boundaryStageToExactVeroneseProj_basicOpen (m d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d), ⊤)) :
    boundaryStageToExactVeroneseProj K n h m ⁻¹ᵁ
      Proj.basicOpen (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)
        (SectionRetainedChartComparison.insertion
          (boundaryLine K m n h) (exactVeroneseStep K n h) d s) =
      sectionGeneratorOpen
        (tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d)) s :=
  SectionRetainedProjOpens.toProj_preimage_basicOpen _ _
    (boundaryExactRetainedGenerated K n h m) s hd

end FLT.Mazur.PolygonInfinitesimalStages
