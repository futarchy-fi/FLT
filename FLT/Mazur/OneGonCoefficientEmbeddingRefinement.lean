/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCoefficientModelRefinement
public import FLT.Mazur.OneGonFiniteCoefficientEmbedding

/-!
# Cartesian refinement of the actual full-cubic character embedding

Refining a coefficient subring changes the whole-cubic embedding by a
Cartesian square. Its full ideal sheaf is retained under this comparison,
without assuming flatness of either inclusion into the original ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates
open WeierstrassIntegralChart OneGonSmoothing CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R G : Type} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)
  (s u : Set R) (h : modelRing t j φ s ≤ modelRing t j φ u)

/-- The whole-curve comparison uses the actual inclusion of the two model subrings. -/
def refinementCurveProjection : integralCurve (equation (modelParameter t j φ u)) ⟶
    integralCurve (equation (modelParameter t j φ s)) := by
  letI := (Subalgebra.inclusion h).toAlgebra
  exact coefficientMorphism (S := modelRing t j φ u) (modelParameter t j φ s)

/-- Full chart refinement commutes after inclusion in the entire cubic. -/
theorem refinementCurveMap :
    Spec.map (CommRingCat.ofHom (CharacterCoefficientCommonRefinement.inclusion h)) ≫
      modelCurveMap t j φ s =
        modelCurveMap t j φ u ≫ refinementCurveProjection t j φ s u h := by
  have hc := chartCoefficientRingMapTo_inclusion (Subalgebra.inclusion h).toRingHom
    (equation (modelParameter t j φ s)) j (equation (modelParameter t j φ u))
    (equation_map (modelParameter t j φ s) (Subalgebra.inclusion h).toRingHom)
  change Spec.map (CommRingCat.ofHom (refinementChartMap t j φ s u h)) ≫
    integralCurveChart (equation (modelParameter t j φ s)) j =
      integralCurveChart (equation (modelParameter t j φ u)) j ≫
        refinementCurveProjection t j φ s u h at hc
  change Spec.map _ ≫ Spec.map _ ≫ _ = (Spec.map _ ≫ _) ≫ _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    refinement_coordinates t j φ s u h, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hc]
  exact (Category.assoc _ _ _).symm

/-- The full model embeddings form a Cartesian square at every coefficient refinement. -/
theorem refinementCurveMap_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (CharacterCoefficientCommonRefinement.inclusion h)))
      (modelCurveMap t j φ u) (modelCurveMap t j φ s)
      (refinementCurveProjection t j φ s u h) := by
  let _ := (Subalgebra.inclusion h).toAlgebra
  have hc : IsPullback
      (Spec.map (CommRingCat.ofHom (CharacterCoefficientCommonRefinement.inclusion h)))
      (modelCurveMap t j φ u ≫ integralCurveStructure (equation (modelParameter t j φ u)))
      (modelCurveMap t j φ s ≫ integralCurveStructure (equation (modelParameter t j φ s)))
      (baseMap (modelRing t j φ s) (modelRing t j φ u)) := by
    rw [modelCurveMap_structure, modelCurveMap_structure]
    exact coefficientMap_isPullback (modelRing t j φ s) (modelRing t j φ u) G
  exact hc.of_bot (refinementCurveMap t j φ s u h)
    (coefficient_isPullback (S := modelRing t j φ u) (modelParameter t j φ s))

/-- The entire model ideal is pulled back along the actual whole-curve refinement. -/
theorem refinementCurveMap_ideal [Finite G]
    (hφ : Function.Surjective (modelCoordinates t j φ s)) :
    (modelCurveMap t j φ u).ker =
      (modelCurveMap t j φ s).ker.comap (refinementCurveProjection t j φ s u h) := by
  let _ := modelCurveMap_isClosedImmersion t j φ s hφ
  let hc := (refinementCurveMap_isPullback t j φ s u h).flip
  rw [← hc.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
