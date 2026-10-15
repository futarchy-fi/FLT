/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageRecovery
public import FLT.Mazur.PolygonArithmeticProjSquare
public import FLT.Mazur.GradedProjZeroMapNaturality
public import FLT.Mazur.SectionRetainedProjBaseCoefficients

/-!
# Original arithmetic coefficients in retained stage recovery

The actual compatible evaluation preserves the original integral coefficients.
Both structural maps of the recovered stage agree by cancellation of the
original coefficient closed immersion. No residue-field lift is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family compatibleEval
  SectionRetainedProjConstruction.toProj SectionRetainedProjStructuralMap.toBase
  exactVeroneseTensorReduction exactVeroneseStep Proj.map GradedProjRingEquiv.iso

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original evaluation into the compatible Proj preserves integral structural scalars. -/
@[reassoc]
theorem boundaryVeroneseProjToCompatible_toBase (m : ℕ) :
    boundaryVeroneseProjToCompatible A π n h hne hgen m ≫
        exactVeroneseProjToBase A π n h hne hgen =
      boundaryRetainedProjToOriginalBase A π hne hgen n h m ≫ baseToIntegral A π m := by
  rw [boundaryRetainedProjToOriginalBase, baseToIntegral,
    SectionRetainedProjBaseCoefficients.toBase_specMap]
  apply GradedProjZeroMapNaturality.map_toSpec
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))
    (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)
    (boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m)
  intro r
  apply Subtype.ext
  change compatibleVeroneseEval A π n h (exactVeroneseStep A π hne hgen n h) m
    (algebraMap A (CompatibleVeroneseSections A π n h
      (exactVeroneseStep A π hne hgen n h)) r) =
      SectionGradedSum.of (boundaryLine A π m n h) ⊤ 0
        (stageScalars A π m n h (Ideal.Quotient.mk (ideal A π ^ (m + 1)) r))
  rw [compatibleVeroneseEval_algebraMap, boundaryIntegralScalars_stage]
  rfl

/-- The structural morphism from graded base change is exactly the original quotient-base map. -/
theorem boundaryRetainedProjToOriginalBase_adic (m : ℕ) :
    boundaryRetainedProjToOriginalBase A π hne hgen n h m =
      boundaryVeroneseProjToAdicBase A π n h hne hgen m := by
  apply (cancel_mono (baseToIntegral A π m)).mp
  rw [← boundaryVeroneseProjToCompatible_toBase]
  exact (exactVeroneseProj_adic_isPullback A π n h hne hgen m).w

end FLT.Mazur.PolygonArithmeticStages
