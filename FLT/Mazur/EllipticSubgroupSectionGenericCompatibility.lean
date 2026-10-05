/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGenericSection
public import FLT.Mazur.EllipticSubgroupClosureSeparated

/-!
# The integral section extends both generic chart presentations

The section selected by a unit Y or Z coordinate agrees with each available
generic chart point. Separatedness also makes every integral section closed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- The left generic chart point extends to the chosen integral section. -/
theorem genericChartPoint_left_section (P : Index A W H 1) :
    genericChartPoint A W H 1 P ≫ closureLeft A W H 1 2 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P.1 := by
  classical
  unfold integralSection
  split_ifs with h
  · rw [genericChartPoint_integral A W H 1 P h, Category.assoc]
  · have hk := ((primitiveLift A W P.1.1).unit_Y_or_Z A W).resolve_left h
    let Q : OverlapIndex A W H 1 2 := ⟨P, by
      rw [coordinateMap_coord, coordinates_ne_zero_iff]
      exact_mod_cast hk.ne_zero⟩
    have he := genericChartPoint_overlap A W H 1 2 Q
    rw [genericChartPoint_integral A W H 2 _ hk, Category.assoc] at he
    exact he

/-- The right generic chart point extends to the same chosen integral section. -/
theorem genericChartPoint_right_section (P : Index A W H 2) :
    genericChartPoint A W H 2 P ≫ closureRight A W H 1 2 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P.1 := by
  classical
  unfold integralSection
  split_ifs with h
  · let Q : OverlapIndex A W H 1 2 :=
      ⟨integralIndex A W H 1 P.1 h, by
        rw [coordinateMap_coord, coordinates_ne_zero_iff]
        exact P.2⟩
    have he := genericChartPoint_overlap A W H 1 2 Q
    rw [genericChartPoint_integral A W H 1 _ h, Category.assoc] at he
    exact he.symm
  · rw [genericChartPoint_integral A W H 2 P
      (((primitiveLift A W P.1.1).unit_Y_or_Z A W).resolve_left h), Category.assoc]

/-- Each constructed integral section is a closed immersion into the separated closure. -/
instance integralSection_isClosedImmersion (P : H) :
    IsClosedImmersion (integralSection A W H P) := by
  have : IsClosedImmersion (integralSection A W H P ≫ closureToBase A W H 1 2) := by
    rw [integralSection_toBase]
    infer_instance
  exact IsClosedImmersion.of_comp _ (closureToBase A W H 1 2)

end FLT.Mazur.EllipticSubgroupChart
