/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionUnchangedLift
public import FLT.Mazur.PolygonCompletePointCanonicalContraction

/-!
# The identity action target in the original full marking section Proj

The entire contraction-side action has a target in the original marking's
full graded section ring. Its constructed unchanged-domain lift commutes with
the original canonical map, retaining the actual line and every graded degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart SectionGradedSum SectionGradedProjConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "L" => completePointLine K n h i
local instance completeIdentityActionSectionLineFact : Fact (LocallyFreeRankOne (L)) :=
  ⟨completePointLine_locallyFreeRankOne K n h i⟩
local notation "e" => completePointCanonicalCubicIso K n h i
local notation "t" => toProj (L) (completePointLine_positivePowerGenerated K n h i)

/-- The full original marking section Proj receives the entire contraction-side action. -/
def completeIdentityActionSectionProjTarget :
    completeIdentityActionProduct K n h i ⟶ Proj (grade (L) ⊤) :=
  completeIdentityActionTarget K n h i ≫ (e).inv

/-- The canonical cubic comparison recovers exactly the constructed action target. -/
@[reassoc] theorem completeIdentityActionSectionProjTarget_cubic :
    completeIdentityActionSectionProjTarget K n h i ≫ (e).hom =
      completeIdentityActionTarget K n h i := by
  rw [completeIdentityActionSectionProjTarget, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- On the whole zero graph, the target is the unchanged original canonical contraction. -/
@[reassoc] theorem completeIdentityActionSectionProjTarget_zero :
    completeIdentityActionZeroGraph K n h i ≫
      completeIdentityActionSectionProjTarget K n h i = (t) := by
  apply (cancel_mono (e).hom).mp
  rw [Category.assoc, completeIdentityActionSectionProjTarget_cubic,
    completeIdentityActionZeroGraph_target, completePointCanonicalCubicIso_contraction]

/-- The actual unchanged-domain lift commutes with the full original section-Proj map. -/
@[reassoc] theorem completeIdentityActionUnchangedLift_sectionProj :
    completeIdentityActionUnchangedLift K n h i ≫
      (completePointIdentityOpen K n h i).ι ≫ (t) =
        (completeIdentityActionUnchangedOpen K n h i).ι ≫
          completeIdentityActionSectionProjTarget K n h i := by
  apply (cancel_mono (e).hom).mp
  simp only [Category.assoc, completePointCanonicalCubicIso_contraction,
    completeIdentityActionSectionProjTarget_cubic,
    completeIdentityActionUnchangedLift_contraction]

end FLT.Mazur.PolygonInfinitesimalStages
