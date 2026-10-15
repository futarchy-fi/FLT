/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentFirstStageParameterEquiv
public import FLT.Mazur.PolygonSmoothingRingMapComposition

/-!
# The finite graph node is the original variable-parameter node

Moving the Laurent parameter into the truncated coefficient ring gives an
isomorphism of the entire original node rings. Both original coordinates,
their joint ideal, and the original truncated-base coefficient map are kept.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "A" => Ring R 1
local notation "S" => Ring R[T;T⁻¹] 1
local notation "t" => C (parameter R 1)
local notation "e" => parameter R[T;T⁻¹] 1

/-- The original finite graph's node coefficient change, retaining both coordinates. -/
def firstNodeParameterMap : ChartRing (t) →+* ChartRing (e) :=
  ringMap (parameterEval R) (t) (e) (parameterEval_parameter R)

/-- The specified node map is bijective on the full nonreduced rings. -/
theorem firstNodeParameterMap_bijective : Function.Bijective (firstNodeParameterMap R) := by
  have hf : Function.Surjective (parameterEval R) := (parameterEquiv R).surjective
  have hi : Function.Injective (parameterEval R) := (parameterEquiv R).injective
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [firstNodeParameterMap, ringMap_ker _ _ _ _ hf,
      (RingHom.injective_iff_ker_eq_bot _).mp hi, Ideal.map_bot]
  · exact ringMap_surjective _ _ _ _ hf

/-- The finite node and original variable-parameter node have exactly the same ring. -/
def firstNodeParameterEquiv : ChartRing (t) ≃+* ChartRing (e) :=
  RingEquiv.ofBijective (firstNodeParameterMap R) (firstNodeParameterMap_bijective R)

/-- The isomorphism is the original coefficient substitution, not a new node identification. -/
theorem firstNodeParameterEquiv_toRingHom :
    (firstNodeParameterEquiv R).toRingHom = firstNodeParameterMap R := rfl

/-- The original left node coordinate is retained. -/
theorem firstNodeParameterEquiv_left :
    firstNodeParameterEquiv R (leftCoordinate (t)) = leftCoordinate (e) := by
  exact ringMap_left (parameterEval R) (t) (e) (parameterEval_parameter R)

/-- The original right node coordinate is retained. -/
theorem firstNodeParameterEquiv_right :
    firstNodeParameterEquiv R (rightCoordinate (t)) = rightCoordinate (e) := by
  exact ringMap_right (parameterEval R) (t) (e) (parameterEval_parameter R)

/-- The full original node ideal is unchanged, without taking its radical. -/
theorem firstNodeParameterEquiv_coordinateIdeal :
    (coordinateIdeal (t)).map (firstNodeParameterEquiv R).toRingHom =
      coordinateIdeal (e) := by
  exact ringMap_coordinateIdeal (parameterEval R) (t) (e) (parameterEval_parameter R)

/-- The original truncated-base structure is retained on every coefficient. -/
theorem firstNodeParameterEquiv_originalScalar (a : A) :
    firstNodeParameterEquiv R (algebraMap (A)[T;T⁻¹] (ChartRing (t)) (C a)) =
      algebraMap (S) (ChartRing (e))
        (stageCoefficientMap (C : R →+* R[T;T⁻¹]) 1 a) := by
  change firstNodeParameterMap R (algebraMap (A)[T;T⁻¹] (ChartRing (t)) (C a)) = _
  rw [firstNodeParameterMap, ringMap_scalar, parameterEval_C]

/-- The actual finite-graph node scheme is the original variable-parameter node scheme. -/
def firstNodeParameterIso : chart (S) (e) ≅ chart (A)[T;T⁻¹] (t) :=
  Scheme.Spec.mapIso (firstNodeParameterEquiv R).toCommRingCatIso.op

/-- This scheme comparison retains exactly the original node coefficient map. -/
theorem firstNodeParameterIso_hom : (firstNodeParameterIso R).hom =
    Spec.map (CommRingCat.ofHom (firstNodeParameterMap R)) := rfl

end FLT.Mazur.PolygonInfinitesimalStages
