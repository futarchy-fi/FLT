/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCoefficientEmbeddingRefinement
public import FLT.Mazur.WeierstrassProperCoefficientComposition

/-!
# Further refinement retains the original curve and full ideal

Direct and iterated refinements use the same literal coefficient inclusions.
Their whole-cubic projections and ideal pullbacks therefore agree. No
functoriality is asserted for the independent choices of finite supports.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates
open WeierstrassIntegralChart OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R G : Type} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)
  (s u v : Set R) (h : modelRing t j φ s ≤ modelRing t j φ u)
  (k : modelRing t j φ u ≤ modelRing t j φ v)

/-- Abstract character inclusion composition keeps concrete model constructions opaque. -/
theorem subalgebra_character_comp {A B C : Subalgebra ℤ R} (hAB : A ≤ B) (hBC : B ≤ C) :
    (CharacterCoefficientCommonRefinement.inclusion (G := G) hBC).comp
      (CharacterCoefficientCommonRefinement.inclusion hAB) =
        CharacterCoefficientCommonRefinement.inclusion (hAB.trans hBC) := by
  rw [CharacterCoefficientCommonRefinement.inclusion,
    CharacterCoefficientCommonRefinement.inclusion, ← AddMonoidAlgebra.mapRingHom_comp]
  rfl

/-- Character coefficient maps compose as the original subring inclusions do. -/
theorem refinementCharacter_comp :
    (CharacterCoefficientCommonRefinement.inclusion (G := G) k).comp
      (CharacterCoefficientCommonRefinement.inclusion h) =
        CharacterCoefficientCommonRefinement.inclusion (h.trans k) :=
  subalgebra_character_comp h k

/-- Direct and iterated whole-cubic projections retain the same coefficient map. -/
@[reassoc] theorem refinementCurveProjection_comp :
    refinementCurveProjection t j φ u v k ≫ refinementCurveProjection t j φ s u h =
      refinementCurveProjection t j φ s v (h.trans k) := by
  exact properCoefficientMap_comp
    (equation (modelParameter t j φ s)) (equation (modelParameter t j φ u))
    (equation (modelParameter t j φ v))
    (Subalgebra.inclusion h).toRingHom (Subalgebra.inclusion k).toRingHom
    (equation_map (modelParameter t j φ s) (Subalgebra.inclusion h).toRingHom).symm
    (equation_map (modelParameter t j φ u) (Subalgebra.inclusion k).toRingHom).symm
    (equation_map (modelParameter t j φ s)
      ((Subalgebra.inclusion k).toRingHom.comp (Subalgebra.inclusion h).toRingHom)).symm

/-- Refining through an intermediate model retains exactly the same full pulled-back ideal. -/
theorem refinement_ideal_comp :
    ((modelCurveMap t j φ s).ker.comap (refinementCurveProjection t j φ s u h)).comap
      (refinementCurveProjection t j φ u v k) =
        (modelCurveMap t j φ s).ker.comap (refinementCurveProjection t j φ s v (h.trans k)) := by
  rw [← Scheme.IdealSheafData.comap_comp, refinementCurveProjection_comp]

/-- The full embedding square survives a further independent enlargement. -/
theorem refinementCurveMap_iterated :
    Spec.map (CommRingCat.ofHom (CharacterCoefficientCommonRefinement.inclusion k)) ≫
      Spec.map (CommRingCat.ofHom (CharacterCoefficientCommonRefinement.inclusion h)) ≫
        modelCurveMap t j φ s =
      modelCurveMap t j φ v ≫ refinementCurveProjection t j φ s v (h.trans k) := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    refinementCharacter_comp]
  exact refinementCurveMap t j φ s v (h.trans k)

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
