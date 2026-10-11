/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleVeroneseStageNaturality
public import FLT.Mazur.PolygonVeroneseStepTransport

/-!
# A shared step for independently chosen coefficient fields

The product of the two exact steps is a common retained step. Both comparisons
preserve the actual original stage maps and their complete coefficient bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] originalStageToMultipleProj exactVeroneseStep
variable (K L : Type) [Field K] [Field L] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Each independently chosen exact step is positive and hence nonzero. -/
instance exactVeroneseStep_neZero : NeZero (exactVeroneseStep K n h) :=
  ⟨Nat.ne_of_gt (exactVeroneseStep_pos K n h)⟩

/-- A common retained step, without equating the two independent exact choices. -/
abbrev commonVeroneseStep : ℕ := exactVeroneseStep K n h * exactVeroneseStep L n h

/-- The first exact step divides the chosen common step. -/
theorem exactStep_dvd_common_left : exactVeroneseStep K n h ∣ commonVeroneseStep K L n h :=
  dvd_mul_right _ _

/-- The second exact step divides the same chosen common step. -/
theorem exactStep_dvd_common_right : exactVeroneseStep L n h ∣ commonVeroneseStep K L n h :=
  dvd_mul_left _ _

/-- The first complete model compared with its actual common-step presentation. -/
def commonVeroneseLeftIso :
    Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) ≅
      Proj (compatibleVeroneseGrade K n h (commonVeroneseStep K L n h)) :=
  multipleVeroneseProjIso K n h _ _ (exactVeroneseStep_pos L n h)

/-- The second complete model compared with the identical numerical common step. -/
def commonVeroneseRightIso :
    Proj (compatibleVeroneseGrade L n h (exactVeroneseStep L n h)) ≅
      Proj (compatibleVeroneseGrade L n h (commonVeroneseStep K L n h)) :=
  multipleVeroneseProjIso L n h _ _ (exactVeroneseStep_pos K n h) ≪≫
    veroneseStepIso L n h _ _ (Nat.mul_comm _ _)

/-- The first comparison retains every original stage morphism. -/
@[reassoc]
theorem commonVeroneseLeftIso_stage (m : ℕ) :
    originalStageToMultipleProj K n h _ (dvd_refl _) m ≫
      (commonVeroneseLeftIso K L n h).hom =
        originalStageToMultipleProj K n h _ (exactStep_dvd_common_left K L n h) m :=
  originalStageToMultipleProj_comparison K n h _ _ (dvd_refl _) m

/-- Product commutativity in the second comparison retains every original stage morphism. -/
@[reassoc]
theorem commonVeroneseRightIso_stage (m : ℕ) :
    originalStageToMultipleProj L n h _ (dvd_refl _) m ≫
      (commonVeroneseRightIso K L n h).hom =
        originalStageToMultipleProj L n h _ (exactStep_dvd_common_right K L n h) m := by
  rw [commonVeroneseRightIso, Iso.trans_hom, ← Category.assoc,
    originalStageToMultipleProj_comparison]
  exact originalStageToMultipleProj_stepIso n h _ _ (Nat.mul_comm _ _) L _ _ m

/-- The first common-step comparison preserves the original complete base. -/
@[reassoc]
theorem commonVeroneseLeftIso_toBase :
    (commonVeroneseLeftIso K L n h).hom ≫
      multipleVeroneseToBase K n h (commonVeroneseStep K L n h) =
        multipleVeroneseToBase K n h (exactVeroneseStep K n h) :=
  multipleVeroneseProjIso_hom_toBase K n h _ _ (exactVeroneseStep_pos L n h)

/-- The second common-step comparison preserves its own original complete base. -/
@[reassoc]
theorem commonVeroneseRightIso_toBase :
    (commonVeroneseRightIso K L n h).hom ≫
      multipleVeroneseToBase L n h (commonVeroneseStep K L n h) =
        multipleVeroneseToBase L n h (exactVeroneseStep L n h) := by
  rw [commonVeroneseRightIso, Iso.trans_hom, Category.assoc]
  change _ ≫ ((veroneseStepIso L n h _ _ _).hom ≫
    GradedProjStructuralMap.toSpecBase _) = _
  rw [veroneseStepIso_toBase]
  exact multipleVeroneseProjIso_hom_toBase L n h _ _ (exactVeroneseStep_pos K n h)

end FLT.Mazur.PolygonInfinitesimalStages
