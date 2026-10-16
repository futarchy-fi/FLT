/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageNodeParameterEquiv
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Moving the parameter at every stage retains the original universal node scaling

The reciprocal source substitution is exactly the universal whole-node
scaling in the original Laurent parameter coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] (m : ℕ)
local notation "t" => parameter R m
local notation "e" => parameter R[T;T⁻¹] m
local notation "b" => ringMap (stageCoefficientMap (C : R →+* R[T;T⁻¹]) m)
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit R m)

/-- The unchanged universal Laurent unit becomes the retained coefficient unit. -/
theorem stageNodeParameter_universalUnit :
    Units.map (parameterEval R m) (PolygonUniversalScaling.u (R := Ring R m)) =
      parameterUnit R m := by
  apply Units.ext
  simpa [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]
    using parameterEval_T_one R m

/-- The original source substitution is the same full universal node map. -/
theorem stageNodeParameterMap_universalScaling :
    (stageNodeParameterMap R m).comp (universalReciprocalScale (t)) =
      (σ).toRingHom.comp (b) := by
  rw [stageNodeParameterMap, universalReciprocalScale, ← RingHom.comp_assoc,
    ringMap_reciprocalScale, stageNodeParameter_universalUnit, RingHom.comp_assoc,
    ringMap_comp]
  have he : (parameterEval R m).comp C = stageCoefficientMap (C : R →+* R[T;T⁻¹]) m :=
    RingHom.ext (parameterEval_C R m)
  simp only [he]

/-- The inverse parameter isomorphism followed by the retained source map is universal scaling. -/
@[reassoc] theorem stageNodeParameterIso_inv_universalScaling :
    (stageNodeParameterIso R m).inv ≫ Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) =
      Spec.map (CommRingCat.ofHom (universalReciprocalScale (t))) := by
  apply (cancel_epi (stageNodeParameterIso R m).hom).mp
  rw [Iso.hom_inv_id_assoc, stageNodeParameterIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, stageNodeParameterMap_universalScaling]

end FLT.Mazur.PolygonInfinitesimalStages
