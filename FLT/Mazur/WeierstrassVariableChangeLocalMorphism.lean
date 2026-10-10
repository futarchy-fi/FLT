/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeLocalCoordinates
public import FLT.Mazur.WeierstrassVariableChangeProjectivePoints
public import FLT.Mazur.WeierstrassIntegralChartProjectivePoint

/-!
# Local cubic morphisms extending an admissible coordinate change

On each transformed-coordinate principal open, normalization gives an actual
map into the original cubic. Its ambient map is the projective linear change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (C : WeierstrassCurve.VariableChange R)

/-- The output chart map on the actual coordinate principal refinement. -/
def variableChangeLocal (j k : Fin 3) :
    Spec (.of (ChangedLocalization W C j k)) ⟶ integralCurve W :=
  integralUnitPoint W (localizedOutput W C j k) (localizedOutput_equation W C j k)
    k (localizedOutputUnit W C j k) (localizedOutputUnit_val W C j k).symm

/-- Restricting the original ambient chart is evaluation at the localized input tuple. -/
theorem localizedInput_projectivePoint (j k : Fin 3) :
    PrincipalAffineRefinement.inclusion (changedCoordinates W C j k) ≫
        projectiveChartMap (C • W) j =
      ProjectiveSpace.unitChartPoint R (Fin 3)
        (algebraMap R (ChangedLocalization W C j k)) (localizedInput W C j k) j 1
        (localizedInput_self W C j k) := by
  rw [projectiveChartMap_eq_unitChartPoint, PrincipalAffineRefinement.inclusion,
    ProjectiveSpace.unitChartPoint_map]
  simp only [← IsScalarTower.algebraMap_eq, map_one, localizedInput]
  rfl

/-- The local cubic morphism is the actual restriction of the projective linear map. -/
@[reassoc] theorem variableChangeLocal_projectiveMap (j k : Fin 3) :
    variableChangeLocal W C j k ≫ integralProjectiveMap W =
      PrincipalAffineRefinement.inclusion (changedCoordinates W C j k) ≫
        projectiveChartMap (C • W) j ≫
          (WeierstrassVariableChangeLinear.projectiveIso C).hom := by
  rw [variableChangeLocal, integralUnitPoint_projectiveMap, ← Category.assoc,
    localizedInput_projectivePoint]
  have h := WeierstrassVariableChangeLinear.unitChartPoint_projectiveIso C
    (algebraMap R (ChangedLocalization W C j k)) (localizedInput W C j k) j k
    1 (localizedOutputUnit W C j k) (localizedInput_self W C j k)
    (by rw [← localizedOutput_eq]; exact (localizedOutputUnit_val W C j k).symm)
  simpa only [← localizedOutput_eq] using h.symm

end FLT.Mazur.WeierstrassIntegralChart
