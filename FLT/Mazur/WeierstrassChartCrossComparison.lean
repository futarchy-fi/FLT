/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartFactorUnit
public import FLT.Mazur.WeierstrassChartUnitLift

/-!
# Comparing different chart presentations by homogeneous coordinates

Equality in the glued curve gives cross-coordinate identities on global sections.
Conversely these identities, together with equality over the coefficient spectrum,
recover the actual overlap and hence equality of the curve-valued morphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {X : Scheme.{u}}

/-- Equal curve-valued maps have proportional normalized coordinates. -/
theorem chart_cross_of_global_eq (j k : Fin 3)
    (f : X ⟶ chartScheme W j) (g : X ⟶ chartScheme W k)
    (h : f ≫ integralCurveChart W j = g ≫ integralCurveChart W k) (i : Fin 3) :
    specSectionHom f (coord W j i) =
      specSectionHom f (coord W j k) * specSectionHom g (coord W k i) := by
  obtain ⟨v, hv, hg⟩ := (integralCurveChart_overlap_isPullback W j k).exists_lift f g h
  rw [← hv, ← hg, ← overlapRestriction_spec, specSectionHom_comp, specSectionHom_comp]
  change specSectionHom v (overlapCoord W j k i) =
    specSectionHom v (overlapCoord W j k k) *
      specSectionHom v (transitionBase W j k (coord W k i))
  rw [← map_mul, transitionBase_coord, ← mul_assoc,
    mul_comm (overlapCoord W j k k), overlapInverse_mul, one_mul]

/-- Cross-coordinate identities and the common coefficient map determine a global point. -/
theorem global_eq_of_chart_cross (j k : Fin 3)
    (f : X ⟶ chartScheme W j) (g : X ⟶ chartScheme W k)
    (hb : f ≫ chartStructure W j = g ≫ chartStructure W k)
    (h : ∀ i, specSectionHom f (coord W j i) =
      specSectionHom f (coord W j k) * specSectionHom g (coord W k i)) :
    f ≫ integralCurveChart W j = g ≫ integralCurveChart W k := by
  have hu : IsUnit (specSectionHom f (coord W j k)) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨specSectionHom g (coord W k j), (h j).symm.trans (by simp)⟩
  obtain ⟨g', hg'⟩ := exists_chart_of_coordinate_unit W j k f hu
  have hc := chart_cross_of_global_eq W j k f g' hg'.symm
  have hbase : g' ≫ chartStructure W k = g ≫ chartStructure W k := by
    rw [← integralCurveChart_structure, ← Category.assoc, hg', Category.assoc,
      integralCurveChart_structure, hb, integralCurveChart_structure]
  let s := g ≫ chartStructure W k
  let _ := specSectionAlgebra s
  have he : specSectionAlgHom s g' hbase = specSectionAlgHom s g rfl := by
    apply hom_ext
    intro i
    exact hu.mul_right_inj.mp ((hc i).symm.trans (h i))
  have he' : g' = g := specSectionHom_injective (congrArg AlgHom.toRingHom he)
  rw [← hg', he']

end FLT.Mazur.WeierstrassIntegralChart
