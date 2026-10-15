/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageProj
public import FLT.Mazur.PolygonArithmeticBoundaryAmple
public import FLT.Mazur.SectionRetainedProjOfAmple

/-!
# Original polygon stages embed in their retained section Proj

The actual ample boundary line constructs a canonical open immersion from
each original polygon stage. Its chart formula uses the original retained
sections, and its basic-open inverse images are their original generator opens.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family
  SectionRetainedProjConstruction.toProj SectionRetainedChartMorphism.toProjOn

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage grading also supplies the generic retained-grading presentation. -/
instance boundaryExactRetainedGradedRing (m : ℕ) :
    GradedRing (RetainedSubringGrading.grade
      (SectionGradedSum.grade (boundaryLine A π m n h) ⊤) (exactVeroneseStep A π hne hgen n h)) :=
  boundaryExactVeroneseGradedRing A π n h hne hgen m

/-- The original ample boundary line generates in the previously constructed exact retained step. -/
theorem boundaryExactRetainedGenerated (m : ℕ) :
    SectionRetainedProjConstruction.PositivePowerGenerated
      (boundaryLine A π m n h) (exactVeroneseStep A π hne hgen n h) :=
  SectionRetainedProjConstruction.positivePowerGenerated_of_ample _ _
    (boundaryLine_ample A π hgen m n h) (exactVeroneseStep_pos A π hne hgen n h)

/-- The actual original polygon stage maps to its independently defined retained section Proj. -/
def boundaryStageToExactVeroneseProj (m : ℕ) :
    (family A π m n h).left ⟶ boundaryExactVeroneseProj A π n h hne hgen m :=
  SectionRetainedProjConstruction.toProj (boundaryLine A π m n h)
    (exactVeroneseStep A π hne hgen n h) (boundaryExactRetainedGenerated A π hne hgen n h m)

/-- The constructed stage map is an open immersion of the original polygon scheme. -/
theorem boundaryStageToExactVeroneseProj_isOpenImmersion (m : ℕ) :
    IsOpenImmersion (boundaryStageToExactVeroneseProj A π hne hgen n h m) :=
  SectionRetainedProjOfAmple.isOpenImmersion (boundaryLine A π m n h) _
    (exactVeroneseStep_pos A π hne hgen n h) (boundaryLine_ample A π hgen m n h)
    (boundaryExactRetainedGenerated A π hne hgen n h m)

/-- Original retained-section generator charts carry the actual intrinsic fraction comparison. -/
theorem boundaryStageToExactVeroneseProj_generator (m d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (boundaryLine A π m n h) (exactVeroneseStep A π hne hgen n h * d), ⊤))
    (U : (family A π m n h).left.Opens)
    (hU : U ≤ sectionGeneratorOpen
      (tensorPower (boundaryLine A π m n h) (exactVeroneseStep A π hne hgen n h * d)) s) :
    U.ι ≫ boundaryStageToExactVeroneseProj A π hne hgen n h m =
      SectionRetainedChartMorphism.toProjOn (boundaryLine A π m n h)
        (exactVeroneseStep A π hne hgen n h) d s hd U hU :=
  (SectionRetainedChartMorphism.toProjOn_eq _ _ _ _ hd
    (boundaryExactRetainedGenerated A π hne hgen n h m) U hU).symm

/-- Every original positive retained section has its exact original generator-open inverse image. -/
theorem boundaryStageToExactVeroneseProj_basicOpen (m d : ℕ) (hd : 0 < d)
    (s : Γ(tensorPower (boundaryLine A π m n h) (exactVeroneseStep A π hne hgen n h * d), ⊤)) :
    boundaryStageToExactVeroneseProj A π hne hgen n h m ⁻¹ᵁ
      Proj.basicOpen (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)
        (SectionRetainedChartComparison.insertion
          (boundaryLine A π m n h) (exactVeroneseStep A π hne hgen n h) d s) =
      sectionGeneratorOpen
        (tensorPower (boundaryLine A π m n h) (exactVeroneseStep A π hne hgen n h * d)) s :=
  SectionRetainedProjOpens.toProj_preimage_basicOpen _ _
    (boundaryExactRetainedGenerated A π hne hgen n h m) s hd

end FLT.Mazur.PolygonArithmeticStages
