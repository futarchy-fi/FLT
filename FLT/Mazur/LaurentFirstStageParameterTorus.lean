/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentFirstStageParameterEquiv
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Retaining the first parameter is an isomorphism of full branch tori

Moving the first Laurent variable into the coefficient ring preserves the
entire second Laurent ring, with an explicit inverse coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentFirstStageParameter
open PolygonInfinitesimalStages PolygonScalingNaturality PolygonSmoothing
variable (R : Type) [CommRing R]
local notation "A" => Ring R 1
local notation "S" => Ring R[T;T⁻¹] 1

/-- The unchanged two-variable ring isomorphism with the first variable in the base. -/
def parameterTorusEquiv : (A)[T;T⁻¹][T;T⁻¹] ≃+* (S)[T;T⁻¹] where
  __ := coeffMap (parameterEval R)
  invFun := coeffMap (parameterUneval R)
  left_inv z := by
    change ((coeffMap (parameterUneval R)).comp (coeffMap (parameterEval R))) z = z
    rw [← coeffMap_comp, parameterUneval_comp_eval, coeffMap_id]
    rfl
  right_inv z := by
    change ((coeffMap (parameterEval R)).comp (coeffMap (parameterUneval R))) z = z
    rw [← coeffMap_comp, parameterEval_comp_uneval, coeffMap_id]
    rfl

/-- The original branch coefficient map is an actual scheme isomorphism. -/
def parameterTorusIso : branchTorus (S) ≅ branchTorus (A)[T;T⁻¹] :=
  Scheme.Spec.mapIso (parameterTorusEquiv R).toCommRingCatIso.op

/-- Its forward morphism is the original coefficient substitution, without alteration. -/
theorem parameterTorusIso_hom : (parameterTorusIso R).hom =
    Spec.map (CommRingCat.ofHom (coeffMap (parameterEval R))) := rfl

instance parameterTorusMap_isIso :
    IsIso (Spec.map (CommRingCat.ofHom (coeffMap (parameterEval R)))) :=
  (parameterTorusIso R).isIso_hom

end FLT.Mazur.LaurentFirstStageParameter
