/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleScalarMaps
public import FLT.Mazur.WeierstrassInfinityHomogeneousComparison

/-!
# Exact scalar reduction of associativity on the true all-infinity member

The two global iterated sums agree if and only if the actual outer chart maps
agree. Equivalently, their normalized X/Z coordinates agree, or the two
homogeneous output minors vanish. No affineness assumption on the source is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Global associativity on this genuine member is precisely equality of its two outer maps. -/
theorem infinityTripleFull_assoc_iff_outputs :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
        infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ ↔
      infinityTripleScalarPoint W hΔ 5 = infinityTripleScalarPoint W hΔ 6 := by
  have ho := infinityTriple_outerOutputs W hΔ (infinityTripleFullMap W hΔ)
    (infinityTripleFullLeft W hΔ) (infinityTripleFullRight W hΔ)
    (infinityTripleFullLeft_inputs W hΔ) (infinityTripleFullRight_inputs W hΔ)
  rw [ho.1, ho.2, ← Category.assoc, ← Category.assoc,
    cancel_mono (integralCurveChart W 1)]
  constructor
  · intro h
    exact specSectionAlgHom_comp_eq (infinityTripleFullBase W hΔ)
      (infinityTripleFullLeft W hΔ) (infinityTripleFullRight W hΔ)
      (infinityTripleFullLeft_base W hΔ) (infinityTripleFullRight_base W hΔ) _ _ h
  · intro h
    exact specSectionAlgHom_compare (infinityTripleFullBase W hΔ)
      (infinityTripleFullLeft W hΔ) (infinityTripleFullRight W hΔ)
      (infinityTripleFullLeft_base W hΔ) (infinityTripleFullRight_base W hΔ)
      (infinityAdditionChart W) (infinityAdditionChart W) h

/-- Exactly two scalar equalities suffice, because both actual outputs are normalized by Y. -/
theorem infinityTripleFull_assoc_iff_coordinates :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
        infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ ↔
      infinityTripleScalarX W hΔ 5 = infinityTripleScalarX W hΔ 6 ∧
        infinityTripleScalarZ W hΔ 5 = infinityTripleScalarZ W hΔ 6 := by
  rw [infinityTripleFull_assoc_iff_outputs]
  exact infinitySpecialization_output_eq_iff W
    (infinityTripleFullLeftAlg W hΔ) (infinityTripleFullRightAlg W hΔ)

/-- Homogeneous comparison is an exact criterion on the full member, with no extra localization. -/
theorem infinityTripleFull_assoc_iff_minors :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
        infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ ↔
      (∀ i ∈ ({0, 2} : Finset (Fin 3)),
        infinityTripleFullLeftAlg W hΔ
            (infinityOutputRestriction W (infinityOutputCoordinates W i)) *
          infinityTripleScalarScale W hΔ 3 =
        infinityTripleFullRightAlg W hΔ
            (infinityOutputRestriction W (infinityOutputCoordinates W i)) *
          infinityTripleScalarScale W hΔ 2) := by
  rw [infinityTripleFull_assoc_iff_outputs]
  exact infinitySpecialization_output_eq_iff_minors W
    (infinityTripleFullLeftAlg W hΔ) (infinityTripleFullRightAlg W hΔ)

end FLT.Mazur.WeierstrassIntegralChart
