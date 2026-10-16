/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentStageParameterEquiv
public import FLT.Mazur.PolygonSmoothingRingMapComposition

/-!
# The higher graph node is the original variable-parameter node

Moving the Laurent parameter into the truncated coefficient ring gives an
isomorphism of the entire original node rings. Both original coordinates,
their joint ideal, and the original truncated-base coefficient map are kept.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "A" => Ring R m
local notation "S" => Ring R[T;T⁻¹] m
local notation "t" => C (parameter R m)
local notation "e" => parameter R[T;T⁻¹] m

/-- The original higher graph's node coefficient change, retaining both coordinates. -/
def stageNodeParameterMap : ChartRing (t) →+* ChartRing (e) :=
  ringMap (parameterEval R m) (t) (e) (parameterEval_parameter R m)

/-- The specified node map is bijective on the full nonreduced rings. -/
theorem stageNodeParameterMap_bijective : Function.Bijective (stageNodeParameterMap R m) := by
  have hf : Function.Surjective (parameterEval R m) := (parameterEquiv R m).surjective
  have hi : Function.Injective (parameterEval R m) := (parameterEquiv R m).injective
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [stageNodeParameterMap, ringMap_ker _ _ _ _ hf,
      (RingHom.injective_iff_ker_eq_bot _).mp hi, Ideal.map_bot]
  · exact ringMap_surjective _ _ _ _ hf

/-- The finite node and original variable-parameter node have exactly the same ring. -/
def stageNodeParameterEquiv : ChartRing (t) ≃+* ChartRing (e) :=
  RingEquiv.ofBijective (stageNodeParameterMap R m) (stageNodeParameterMap_bijective R m)

/-- The isomorphism is the original coefficient substitution, not a new node identification. -/
theorem stageNodeParameterEquiv_toRingHom :
    (stageNodeParameterEquiv R m).toRingHom = stageNodeParameterMap R m := rfl

/-- The original left node coordinate is retained. -/
theorem stageNodeParameterEquiv_left :
    stageNodeParameterEquiv R m (leftCoordinate (t)) = leftCoordinate (e) := by
  exact ringMap_left (parameterEval R m) (t) (e) (parameterEval_parameter R m)

/-- The original right node coordinate is retained. -/
theorem stageNodeParameterEquiv_right :
    stageNodeParameterEquiv R m (rightCoordinate (t)) = rightCoordinate (e) := by
  exact ringMap_right (parameterEval R m) (t) (e) (parameterEval_parameter R m)

/-- The full original node ideal is unchanged, without taking its radical. -/
theorem stageNodeParameterEquiv_coordinateIdeal :
    (coordinateIdeal (t)).map (stageNodeParameterEquiv R m).toRingHom =
      coordinateIdeal (e) := by
  exact ringMap_coordinateIdeal (parameterEval R m) (t) (e) (parameterEval_parameter R m)

/-- The original truncated-base structure is retained on every coefficient. -/
theorem stageNodeParameterEquiv_originalScalar (a : A) :
    stageNodeParameterEquiv R m (algebraMap (A)[T;T⁻¹] (ChartRing (t)) (C a)) =
      algebraMap (S) (ChartRing (e))
        (stageCoefficientMap (C : R →+* R[T;T⁻¹]) m a) := by
  change stageNodeParameterMap R m (algebraMap (A)[T;T⁻¹] (ChartRing (t)) (C a)) = _
  rw [stageNodeParameterMap, ringMap_scalar, parameterEval_C]

/-- The actual finite-graph node scheme is the original variable-parameter node scheme. -/
def stageNodeParameterIso : chart (S) (e) ≅ chart (A)[T;T⁻¹] (t) :=
  Scheme.Spec.mapIso (stageNodeParameterEquiv R m).toCommRingCatIso.op

/-- This scheme comparison retains exactly the original node coefficient map. -/
theorem stageNodeParameterIso_hom : (stageNodeParameterIso R m).hom =
    Spec.map (CommRingCat.ofHom (stageNodeParameterMap R m)) := rfl

end FLT.Mazur.PolygonInfinitesimalStages
