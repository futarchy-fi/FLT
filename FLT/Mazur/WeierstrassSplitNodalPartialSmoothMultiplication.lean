/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalSmoothChartCoordinates
public import FLT.Mazur.WeierstrassSplitNodalOrdinaryScheme
public import FLT.Mazur.WeierstrassSplitNodalReciprocalScheme
public import FLT.Mazur.WeierstrassPartialFieldPointComparison

/-!
# All four original charts agree with full smooth nodal multiplication

For any common source scheme and coefficient ring, the actual partial addition
of smooth inputs equals multiplication in the constructed full smooth group.
The inputs need only agree as morphisms into the original cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (a : Rˣ) (i : AdditionChartIndex) (s : X ⟶ Spec (.of R))
  (f : X ⟶ Spec (additionChartRing (splitNodalEquation a) i))
  (v w : Over.mk s ⟶ splitNodalSmoothOver a)
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing (splitNodalEquation a) i))) = s)
  (hl : (f ≫ Spec.map (CommRingCat.ofHom
      (additionInputLeft (splitNodalEquation a) i).toRingHom)) ≫
      integralCurveChart (splitNodalEquation a) 2 =
    v.left ≫ (integralSmoothOpen (splitNodalEquation a)).ι)
  (hr : (f ≫ Spec.map (CommRingCat.ofHom
      (additionInputRight (splitNodalEquation a) i).toRingHom)) ≫
      integralCurveChart (splitNodalEquation a) 2 =
    w.left ≫ (integralSmoothOpen (splitNodalEquation a)).ι)

include hf hl hr

/-- Every original addition chart is the restriction of the full smooth group multiplication. -/
theorem splitNodal_chart_smooth_multiplication :
    let _ := splitNodalSmoothCommGrpObj a
    f ≫ additionCurveChart (splitNodalEquation a) i =
      (lift v w ≫ μ[splitNodalSmoothOver a]).left ≫
        (integralSmoothOpen (splitNodalEquation a)).ι := by
  let _ := specSectionAlgebra s
  let _ := splitNodalSmoothCommGrpObj a
  obtain ⟨p, hp, hv⟩ := splitNodalSmooth_exists_chart a s v
  obtain ⟨q, hq, hw⟩ := splitNodalSmooth_exists_chart a s w
  have hl' := hl.trans hv
  have hr' := hr.trans hw
  dsimp only
  rw [splitNodalSmooth_multiplication_chart_coordinates a s v w p q hp hq hv hw]
  cases i
  · exact splitNodalOrdinary_commonScheme a false s f p q hf hp hq hl' hr'
  · exact splitNodalOrdinary_commonScheme a true s f p q hf hp hq hl' hr'
  · exact splitNodalReciprocal_commonScheme a false s f p q hf hp hq hl' hr'
  · exact splitNodalReciprocal_commonScheme a true s f p q hf hp hq hl' hr'

/-- The original partial addition, on every chart, is the full smooth group multiplication. -/
theorem splitNodal_partial_smooth_multiplication :
    let _ := splitNodalSmoothCommGrpObj a
    f ≫ additionChartToDomain (splitNodalEquation a) i ≫
        affinePartialAddition (splitNodalEquation a) =
      (lift v w ≫ μ[splitNodalSmoothOver a]).left ≫
        (integralSmoothOpen (splitNodalEquation a)).ι := by
  let _ := splitNodalSmoothCommGrpObj a
  dsimp only
  rw [additionChartToDomain_addition]
  exact splitNodal_chart_smooth_multiplication a i s f v w hf hl hr

/-- Each partial-chart output of smooth inputs factors through the entire relative smooth locus. -/
theorem splitNodal_chart_output_smooth :
    ∃ t : X ⟶ (integralSmoothOpen (splitNodalEquation a)).toScheme,
      t ≫ (integralSmoothOpen (splitNodalEquation a)).ι =
        f ≫ additionCurveChart (splitNodalEquation a) i := by
  let _ := splitNodalSmoothCommGrpObj a
  exact ⟨(lift v w ≫ μ[splitNodalSmoothOver a]).left,
    (splitNodal_chart_smooth_multiplication a i s f v w hf hl hr).symm⟩

end FLT.Mazur.WeierstrassIntegralChart
