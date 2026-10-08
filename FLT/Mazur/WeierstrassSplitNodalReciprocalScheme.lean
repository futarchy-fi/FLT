/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalReciprocalMultiplication
public import FLT.Mazur.WeierstrassChartCrossComparison
public import FLT.Mazur.WeierstrassAffinePartialAddition

/-!
# Reciprocal nodal multiplication on arbitrary common schemes

Equality of the actual input morphisms implies that the reciprocal output
is the torus point with the product Laurent unit in global sections. The
source need not be affine or reduced, and the coefficient ring is arbitrary.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (a : Rˣ) (b : Bool)
  (s : X ⟶ Spec (.of R))
  (f : X ⟶ Spec (additionChartRing (splitNodalEquation a) (reciprocalIndex b)))
  (p q : X ⟶ chartScheme (splitNodalEquation a) 1)
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing (splitNodalEquation a) (reciprocalIndex b)))) = s)
  (hp : p ≫ chartStructure (splitNodalEquation a) 1 = s)
  (hq : q ≫ chartStructure (splitNodalEquation a) 1 = s)
  (hl : (f ≫ Spec.map (CommRingCat.ofHom
      (reciprocalInputLeft (splitNodalEquation a) b).toRingHom)) ≫
      integralCurveChart (splitNodalEquation a) 2 =
    p ≫ integralCurveChart (splitNodalEquation a) 1)
  (hr : (f ≫ Spec.map (CommRingCat.ofHom
      (reciprocalInputRight (splitNodalEquation a) b).toRingHom)) ≫
      integralCurveChart (splitNodalEquation a) 2 =
    q ≫ integralCurveChart (splitNodalEquation a) 1)

include hf hl hr

/-- The actual reciprocal output is the torus image of the product of its common-input units. -/
theorem splitNodalReciprocal_commonScheme :
    let _ := specSectionAlgebra s
    let P := specSectionAlgHom s p hp
    let Q := specSectionAlgHom s q hq
    f ≫ additionCurveChart (splitNodalEquation a) (reciprocalIndex b) =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R)
        (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom ≫
          splitNodalTorusToCurve a := by
  let _ := specSectionAlgebra s
  let F := specSectionAlgHom
    (A := additionChartRing (splitNodalEquation a) (reciprocalIndex b)) s f hf
  let P := specSectionAlgHom s p hp
  let Q := specSectionAlgHom s q hq
  have hP (i : Fin 3) : F (reciprocalInputLeft (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 i)) =
      F (reciprocalInputLeft (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 1)) * P (coord (splitNodalEquation a) 1 i) := by
    have h := chart_cross_of_global_eq (splitNodalEquation a) 2 1 _ p hl i
    rw [specSectionHom_comp] at h
    cases b <;> exact h
  have hQ (i : Fin 3) : F (reciprocalInputRight (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 i)) =
      F (reciprocalInputRight (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 1)) * Q (coord (splitNodalEquation a) 1 i) := by
    have h := chart_cross_of_global_eq (splitNodalEquation a) 2 1 _ q hr i
    rw [specSectionHom_comp] at h
    cases b <;> exact h
  have he := splitNodalReciprocal_chart_multiplication a b F P Q hP hQ
  have hm : f ≫ Spec.map (CommRingCat.ofHom
        (reciprocalChartAddition (splitNodalEquation a) b).toRingHom) =
      specSectionMorphism (splitNodalUnitChart a
        (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom := by
    apply specSectionHom_injective
    rw [specSectionHom_comp, specSectionHom_morphism]
    exact congrArg AlgHom.toRingHom he
  have hc : additionCurveChart (splitNodalEquation a) (reciprocalIndex b) =
      Spec.map (CommRingCat.ofHom
        (reciprocalChartAddition (splitNodalEquation a) b).toRingHom) ≫
          integralCurveChart (splitNodalEquation a) 1 := by cases b <;> rfl
  dsimp only
  rw [hc, ← Category.assoc, hm]
  change specSectionMorphism
    ((LaurentUnitPoints.evalUnit (R := R)
      (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom.comp
        (splitNodalChartToLaurent a).toRingHom) ≫ _ = _
  rw [specSectionMorphism_comp, Category.assoc]
  rfl

/-- The same common-scheme comparison applies to the original partial addition morphism. -/
theorem splitNodalReciprocal_partial_commonScheme :
    let _ := specSectionAlgebra s
    let P := specSectionAlgHom s p hp
    let Q := specSectionAlgHom s q hq
    f ≫ additionChartToDomain (splitNodalEquation a) (reciprocalIndex b) ≫
        affinePartialAddition (splitNodalEquation a) =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R)
        (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom ≫
          splitNodalTorusToCurve a := by
  let _ := specSectionAlgebra s
  dsimp only
  rw [additionChartToDomain_addition]
  exact splitNodalReciprocal_commonScheme a b s f p q hf hp hq hl hr

end FLT.Mazur.WeierstrassIntegralChart
