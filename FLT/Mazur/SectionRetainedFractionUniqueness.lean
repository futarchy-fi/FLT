/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedFractionEquation

/-!
# Uniqueness of the intrinsic retained fraction value

An invertible denominator makes the original section equation determine
its scalar uniquely, independently of the retained fraction presentation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedFractionUniqueness

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y : Scheme} (p : Y ⟶ X) (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (e : (pullback p).obj L ≅ structureModule Y)
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- The original numerator-denominator section equation uniquely determines a retained value. -/
theorem eq_evaluation (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (SectionRetainedProjChart.ringHom p L e q f))
    (c : NumDenSameDeg (RetainedSubringGrading.grade (grade L ⊤) q) (Submonoid.powers f))
    {d : ℕ} (s t : Γ(tensorPower L d, ⊤))
    (hs : of L ⊤ d s = c.den.val.val) (ht : of L ⊤ d t = c.num.val.val)
    (a : Γ(Y, ⊤))
    (ha : a • pullGlobal p (tensorPower L d) s = pullGlobal p (tensorPower L d) t) :
    a = GradedProjUnitChart.evaluation _ (SectionRetainedProjChart.ringHom p L e q)
      f hf (HomogeneousLocalization.mk c) := by
  have he := congrArg ((tensorPowerIso p L d).hom.app ⊤) ha
  rw [Hom.app_smul] at he
  have hd := (SectionGradedCoordinateEvaluation.coordinate_equation_iff e ⊤ d _ _ _).mpr he
  apply (GradedProjUnitChart.denominator_isUnit _
    (SectionRetainedProjChart.ringHom p L e q) f hf c).mul_left_inj.mp
  rw [GradedProjUnitChart.evaluation_mk_mul]
  change a * SectionGradedProjChart.ringHom p L e c.den.val.val =
    SectionGradedProjChart.ringHom p L e c.num.val.val
  rw [← hs, ← ht, SectionGradedProjChart.ringHom_of, SectionGradedProjChart.ringHom_of]
  exact hd

end FLT.Mazur.SectionRetainedFractionUniqueness
