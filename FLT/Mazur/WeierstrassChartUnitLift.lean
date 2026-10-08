/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralProductOverlap
public import FLT.Mazur.WeierstrassSpecSectionMorphism

/-!
# Changing a chart when its transition coordinate is a unit

This construction works for arbitrary source schemes. It will supply the five
affine presentations after localizing the actual infinity triple coordinates.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {X : Scheme.{u}}

/-- A unit transition coordinate gives a presentation in the other chart. -/
theorem exists_chart_of_coordinate_unit (j k : Fin 3) (f : X ⟶ chartScheme W j)
    (h : IsUnit (specSectionHom f (coord W j k))) :
    ∃ g : X ⟶ chartScheme W k,
      g ≫ integralCurveChart W k = f ≫ integralCurveChart W j := by
  let a : Overlap W j k →+* Γ(X, ⊤) :=
    IsLocalization.Away.lift (coord W j k) h
  let v : X ⟶ overlapScheme W j k := specSectionMorphism a
  have hv : v ≫ overlapInclusion W j k = f := by
    rw [← overlapRestriction_spec]
    apply specSectionHom_injective
    rw [specSectionHom_comp, specSectionHom_morphism]
    exact IsLocalization.Away.lift_comp (coord W j k) h
  refine ⟨v ≫ chartTransition W j k ≫ overlapInclusion W k j, ?_⟩
  simp only [Category.assoc, integralCurveChart_compatibility]
  rw [← Category.assoc, hv]

end FLT.Mazur.WeierstrassIntegralChart
