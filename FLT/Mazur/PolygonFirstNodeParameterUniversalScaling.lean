/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeParameterEquiv
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Moving the first parameter retains the original universal node scaling

The reciprocal source substitution is exactly the universal whole-node
scaling in the original Laurent parameter coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R]
local notation "t" => parameter R 1
local notation "e" => parameter R[T;T⁻¹] 1
local notation "b" => ringMap (stageCoefficientMap (C : R →+* R[T;T⁻¹]) 1)
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit R)

/-- The unchanged universal Laurent unit becomes the retained coefficient unit. -/
theorem firstNodeParameter_universalUnit :
    Units.map (parameterEval R) (PolygonUniversalScaling.u (R := Ring R 1)) =
      parameterUnit R := by
  apply Units.ext
  simpa [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]
    using parameterEval_T_one R

/-- The original source substitution is the same full universal node map. -/
theorem firstNodeParameterMap_universalScaling :
    (firstNodeParameterMap R).comp (universalReciprocalScale (t)) =
      (σ).toRingHom.comp (b) := by
  rw [firstNodeParameterMap, universalReciprocalScale, ← RingHom.comp_assoc,
    ringMap_reciprocalScale, firstNodeParameter_universalUnit, RingHom.comp_assoc,
    ringMap_comp]
  have he : (parameterEval R).comp C = stageCoefficientMap (C : R →+* R[T;T⁻¹]) 1 :=
    RingHom.ext (parameterEval_C R)
  simp only [he]

/-- The inverse parameter isomorphism followed by the retained source map is universal scaling. -/
@[reassoc] theorem firstNodeParameterIso_inv_universalScaling :
    (firstNodeParameterIso R).inv ≫ Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) =
      Spec.map (CommRingCat.ofHom (universalReciprocalScale (t))) := by
  apply (cancel_epi (firstNodeParameterIso R).hom).mp
  rw [Iso.hom_inv_id_assoc, firstNodeParameterIso_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, firstNodeParameterMap_universalScaling]

end FLT.Mazur.PolygonInfinitesimalStages
