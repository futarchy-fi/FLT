/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentStageParameterEquiv
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Retaining an arbitrary-stage parameter is an isomorphism of full branch tori

Moving the first Laurent variable at any truncated stage into the coefficient ring preserves the
entire second Laurent ring, with an explicit inverse coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentStageParameter
open PolygonInfinitesimalStages PolygonScalingNaturality PolygonSmoothing
variable (R : Type) [CommRing R] (m : ℕ)
local notation "A" => Ring R m
local notation "S" => Ring R[T;T⁻¹] m

/-- The unchanged two-variable ring isomorphism with the first variable in the base. -/
def parameterTorusEquiv : (A)[T;T⁻¹][T;T⁻¹] ≃+* (S)[T;T⁻¹] where
  __ := coeffMap (parameterEval R m)
  invFun := coeffMap (parameterUneval R m)
  left_inv z := by
    change ((coeffMap (parameterUneval R m)).comp (coeffMap (parameterEval R m))) z = z
    rw [← coeffMap_comp, parameterUneval_comp_eval, coeffMap_id]
    rfl
  right_inv z := by
    change ((coeffMap (parameterEval R m)).comp (coeffMap (parameterUneval R m))) z = z
    rw [← coeffMap_comp, parameterEval_comp_uneval, coeffMap_id]
    rfl

/-- The original branch coefficient map is an actual scheme isomorphism. -/
def parameterTorusIso : branchTorus (S) ≅ branchTorus (A)[T;T⁻¹] :=
  Scheme.Spec.mapIso (parameterTorusEquiv R m).toCommRingCatIso.op

/-- Its forward morphism is the original coefficient substitution, without alteration. -/
theorem parameterTorusIso_hom : (parameterTorusIso R m).hom =
    Spec.map (CommRingCat.ofHom (coeffMap (parameterEval R m))) := rfl

instance parameterTorusMap_isIso :
    IsIso (Spec.map (CommRingCat.ofHom (coeffMap (parameterEval R m)))) :=
  (parameterTorusIso R m).isIso_hom

end FLT.Mazur.LaurentStageParameter
