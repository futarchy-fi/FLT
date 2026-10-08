/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalOrdinaryAlgebraMultiplication
public import FLT.Mazur.WeierstrassChartCrossComparison
public import FLT.Mazur.WeierstrassAffinePartialAddition

/-!
# Ordinary nodal multiplication on arbitrary common schemes

Equality of the actual input morphisms implies that the ordinary output
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
  (f : X ⟶ Spec (additionChartRing (splitNodalEquation a) (ordinaryIndex b)))
  (p q : X ⟶ chartScheme (splitNodalEquation a) 1)
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing (splitNodalEquation a) (ordinaryIndex b)))) = s)
  (hp : p ≫ chartStructure (splitNodalEquation a) 1 = s)
  (hq : q ≫ chartStructure (splitNodalEquation a) 1 = s)
  (hl : (f ≫ Spec.map (CommRingCat.ofHom
      (ordinaryInputLeft (splitNodalEquation a) b).toRingHom)) ≫
      integralCurveChart (splitNodalEquation a) 2 =
    p ≫ integralCurveChart (splitNodalEquation a) 1)
  (hr : (f ≫ Spec.map (CommRingCat.ofHom
      (ordinaryInputRight (splitNodalEquation a) b).toRingHom)) ≫
      integralCurveChart (splitNodalEquation a) 2 =
    q ≫ integralCurveChart (splitNodalEquation a) 1)

include hf hl hr

/-- The actual ordinary output is the torus image of the product of its common-input units. -/
theorem splitNodalOrdinary_commonScheme :
    let _ := specSectionAlgebra s
    let P := specSectionAlgHom s p hp
    let Q := specSectionAlgHom s q hq
    f ≫ additionCurveChart (splitNodalEquation a) (ordinaryIndex b) =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R)
        (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom ≫
          splitNodalTorusToCurve a := by
  let _ := specSectionAlgebra s
  let F := specSectionAlgHom
    (A := additionChartRing (splitNodalEquation a) (ordinaryIndex b)) s f hf
  let P := specSectionAlgHom s p hp
  let Q := specSectionAlgHom s q hq
  have hP (i : Fin 3) : F (ordinaryInputLeft (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 i)) =
      F (ordinaryInputLeft (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 1)) * P (coord (splitNodalEquation a) 1 i) := by
    have h := chart_cross_of_global_eq (splitNodalEquation a) 2 1 _ p hl i
    rw [specSectionHom_comp] at h
    cases b <;> exact h
  have hQ (i : Fin 3) : F (ordinaryInputRight (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 i)) =
      F (ordinaryInputRight (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 1)) * Q (coord (splitNodalEquation a) 1 i) := by
    have h := chart_cross_of_global_eq (splitNodalEquation a) 2 1 _ q hr i
    rw [specSectionHom_comp] at h
    cases b <;> exact h
  let o := f ≫ Spec.map (CommRingCat.ofHom
    (ordinaryChartAddition (splitNodalEquation a) b).toRingHom)
  have ho : IsUnit (specSectionHom o (coord (splitNodalEquation a) 2 1)) := by
    rw [specSectionHom_comp]
    exact splitNodalOrdinary_output_y_isUnit a b F P Q hP hQ
  obtain ⟨t, ht⟩ := exists_chart_of_coordinate_unit (splitNodalEquation a) 2 1 o ho
  have hb : t ≫ chartStructure (splitNodalEquation a) 1 = s := by
    rw [← integralCurveChart_structure, ← Category.assoc, ht, Category.assoc,
      integralCurveChart_structure]
    change (f ≫ Spec.map (CommRingCat.ofHom
      (ordinaryChartAddition (splitNodalEquation a) b).toRingHom)) ≫ _ = _
    rw [Category.assoc, chartStructure, ← Spec.map_comp]
    convert hf using 1
    congr 2
    exact CommRingCat.hom_ext (AlgHom.comp_algebraMap _)
  let T := specSectionAlgHom s t hb
  have hT (i : Fin 3) : F (ordinaryChartAddition (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 i)) =
      F (ordinaryChartAddition (splitNodalEquation a) b
        (coord (splitNodalEquation a) 2 1)) * T (coord (splitNodalEquation a) 1 i) := by
    have h := chart_cross_of_global_eq (splitNodalEquation a) 2 1 o t ht.symm i
    dsimp only [o] at h
    rw [specSectionHom_comp] at h
    cases b <;> exact h
  have he := splitNodalOrdinary_chart_multiplication a b F P Q hP hQ T hT
  have hm : t = specSectionMorphism (splitNodalUnitChart a
        (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom := by
    apply specSectionHom_injective
    rw [specSectionHom_morphism]
    exact congrArg AlgHom.toRingHom he
  have hc : additionCurveChart (splitNodalEquation a) (ordinaryIndex b) =
      Spec.map (CommRingCat.ofHom
        (ordinaryChartAddition (splitNodalEquation a) b).toRingHom) ≫
          integralCurveChart (splitNodalEquation a) 2 := by cases b <;> rfl
  dsimp only
  rw [hc, ← Category.assoc]
  change o ≫ integralCurveChart (splitNodalEquation a) 2 = _
  rw [← ht, hm]
  change specSectionMorphism
    ((LaurentUnitPoints.evalUnit (R := R)
      (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom.comp
        (splitNodalChartToLaurent a).toRingHom) ≫ _ = _
  rw [specSectionMorphism_comp, Category.assoc]
  rfl

/-- The same common-scheme comparison applies to the original partial addition morphism. -/
theorem splitNodalOrdinary_partial_commonScheme :
    let _ := specSectionAlgebra s
    let P := specSectionAlgHom s p hp
    let Q := specSectionAlgHom s q hq
    f ≫ additionChartToDomain (splitNodalEquation a) (ordinaryIndex b) ≫
        affinePartialAddition (splitNodalEquation a) =
      specSectionMorphism (LaurentUnitPoints.evalUnit (R := R)
        (splitNodalChartUnit a P * splitNodalChartUnit a Q)).toRingHom ≫
          splitNodalTorusToCurve a := by
  let _ := specSectionAlgebra s
  dsimp only
  rw [additionChartToDomain_addition]
  exact splitNodalOrdinary_commonScheme a b s f p q hf hp hq hl hr

end FLT.Mazur.WeierstrassIntegralChart
