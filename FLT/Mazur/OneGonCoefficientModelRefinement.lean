/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFiniteCoefficientRecovery
public import FLT.Mazur.CharacterCoefficientCommonRefinement
public import FLT.Mazur.WeierstrassChartArithmeticRestriction

/-!
# Refinement of the full one-gon model coordinate map

Independent supports for a fixed original character embedding can be compared
inside any larger model ring. The chart square is an equality of full ring
homomorphisms, retaining every nilpotent coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates
open WeierstrassIntegralChart OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R G : Type} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)
  (s u : Set R) (h : modelRing t j φ s ≤ modelRing t j φ u)

/-- Character recovery through abstract subalgebras is literal coefficient inclusion. -/
theorem subalgebra_character_recovery {A B : Subalgebra ℤ R} (hAB : A ≤ B) :
    (AddMonoidAlgebra.mapRingHom G B.val.toRingHom).comp
      (CharacterCoefficientCommonRefinement.inclusion hAB) =
        AddMonoidAlgebra.mapRingHom G A.val.toRingHom := by
  rw [CharacterCoefficientCommonRefinement.inclusion, ← AddMonoidAlgebra.mapRingHom_comp]
  rfl

/-- Abstract coordinate squares are determined by the actual normalized coordinate values. -/
theorem characterChartSquare {A B : Type} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (V : WeierstrassCurve B) (f : A →+* B) (hf : W.map f = V)
    (l : Fin 3) (p : Coordinate W l →ₐ[A] AddMonoidAlgebra A G)
    (q : Coordinate V l →ₐ[B] AddMonoidAlgebra B G)
    (hp : ∀ i, AddMonoidAlgebra.mapRingHom G f (p (coord W l i)) = q (coord V l i)) :
    (AddMonoidAlgebra.mapRingHom G f).comp p.toRingHom =
      q.toRingHom.comp (chartCoefficientRingMapTo f W l V hf) := by
  apply chartRingHom_ext W l
  · intro a
    change AddMonoidAlgebra.mapRingHom G f (p (algebraMap A _ a)) =
      q (chartCoefficientRingMapTo f W l V hf (algebraMap A _ a))
    rw [AlgHom.commutes, chartCoefficientRingMapTo_scalar, AlgHom.commutes]
    exact RingHom.congr_fun (AddMonoidAlgebra.mapRingHom_comp_algebraMap f) a
  · intro i
    change AddMonoidAlgebra.mapRingHom G f (p (coord W l i)) =
      q (chartCoefficientRingMapTo f W l V hf (coord W l i))
    rw [chartCoefficientRingMapTo_coord]
    exact hp i

/-- A larger actual coefficient model retains the specified smoothing parameter. -/
theorem refinement_parameter :
    Subalgebra.inclusion h (modelParameter t j φ s) = modelParameter t j φ u := rfl

/-- The chart comparison uses the literal inclusion of the two coefficient subrings. -/
def refinementChartMap : Coordinate (equation (modelParameter t j φ s)) j →+*
    Coordinate (equation (modelParameter t j φ u)) j :=
  chartCoefficientRingMapTo (Subalgebra.inclusion h).toRingHom
    (equation (modelParameter t j φ s)) j (equation (modelParameter t j φ u))
    (equation_map (modelParameter t j φ s) (Subalgebra.inclusion h).toRingHom)

/-- Character inclusion through an intermediate coefficient model is the original inclusion. -/
theorem refinement_inclusion (x : AddMonoidAlgebra (modelRing t j φ s) G) :
    modelInclusion t j φ u (CharacterCoefficientCommonRefinement.inclusion h x) =
      modelInclusion t j φ s x :=
  RingHom.congr_fun (subalgebra_character_recovery (G := G) h) x

/-- Every normalized coordinate agrees before recovery to the original ring. -/
theorem refinement_values (i : Fin 3) :
    CharacterCoefficientCommonRefinement.inclusion h (modelValues t j φ s i) =
      modelValues t j φ u i := by
  apply CharacterFiniteCoefficientModel.inclusion_injective (values t j φ) (u ∪ {t})
  rw [refinement_inclusion t j φ s u h, modelValues_recovery t j φ s,
    modelValues_recovery t j φ u]

/-- The constructed model algebra map has the specified full coordinate images. -/
theorem modelCoordinates_coord (i : Fin 3) :
    modelCoordinates t j φ s (coord (equation (modelParameter t j φ s)) j i) =
      modelValues t j φ s i := evaluation_coord ..

/-- The entire affine chart embedding commutes with refinement of its coefficient model. -/
theorem refinement_coordinates :
    (CharacterCoefficientCommonRefinement.inclusion h).comp
      (modelCoordinates t j φ s).toRingHom =
        (modelCoordinates t j φ u).toRingHom.comp (refinementChartMap t j φ s u h) := by
  apply characterChartSquare
  intro i
  rw [modelCoordinates_coord t j φ s, modelCoordinates_coord t j φ u]
  exact refinement_values t j φ s u h i

/-- Refinement contracts the entire embedding ideal, without taking its radical. -/
theorem refinement_kernel :
    RingHom.ker (modelCoordinates t j φ s).toRingHom =
      (RingHom.ker (modelCoordinates t j φ u).toRingHom).comap
        (refinementChartMap t j φ s u h) := by
  ext x
  change modelCoordinates t j φ s x = 0 ↔
    modelCoordinates t j φ u (refinementChartMap t j φ s u h x) = 0
  have he := RingHom.congr_fun (refinement_coordinates t j φ s u h) x
  change CharacterCoefficientCommonRefinement.inclusion h (modelCoordinates t j φ s x) =
    modelCoordinates t j φ u (refinementChartMap t j φ s u h x) at he
  rw [← he]
  exact (map_eq_zero_iff _ (CharacterCoefficientCommonRefinement.inclusion_injective h)).symm

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
