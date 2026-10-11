/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothSevenPoints
public import FLT.Mazur.WeierstrassLeftSmoothFiveRegularSectionDescent

/-!
# Associativity of the smooth action on the whole integral cubic

The five regular input and intermediate coordinates give injective localization
on simultaneous Y/Z presentations. Descent proves the actual action identity,
including singular points and nilpotents over every coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The first five members are precisely the original inputs and intermediate sums. -/
theorem leftSmoothTripleSevenPoint_firstFive {X : Scheme.{u}} (t : X ⟶ leftSmoothTriple W)
    (i : Fin 5) :
    t ≫ leftSmoothTripleSevenPoint W (i.castAdd 2) = leftSmoothTripleFivePoint W t i := by
  fin_cases i <;> simp [leftSmoothTripleSevenPoint, leftSmoothTripleFivePoint]

/-- Actual iterated sums agree on every flat affine simultaneous chart presentation. -/
theorem leftSmoothTripleAdd_of_sevenCharts {S : Type u} [CommRing S]
    (t : Spec (.of S) ⟶ leftSmoothTriple W) [Flat t] (b : Fin 7 → Bool)
    (p : (i : Fin 7) → Spec (.of S) ⟶ chartScheme W (productChartCoordinate (b i)))
    (hp : ∀ i, p i ≫ integralCurveChart W (productChartCoordinate (b i)) =
      t ≫ leftSmoothTripleSevenPoint W i) :
    t ≫ leftSmoothTripleAddLeft W = t ≫ leftSmoothTripleAddRight W := by
  apply leftSmoothTripleAdd_of_fiveRegularSections W t
    (fun i => productChartCoordinate (b (i.castAdd 2))) (fun i => p (i.castAdd 2))
    (fun i => (hp _).trans (leftSmoothTripleSevenPoint_firstFive W t i))
    (leftSmoothTripleSevenPoint_z_regular W t b p hp)
    (productChartCoordinate (b 5)) (productChartCoordinate (b 6)) (p 5) (p 6)
  · exact hp 5
  · exact hp 6

/-- Two smooth inputs act associatively on every point of the whole original integral cubic. -/
theorem leftSmoothFactorAddition_assoc :
    leftSmoothTripleAddLeft W = leftSmoothTripleAddRight W := by
  apply leftSmoothTripleAdd_eq_of_chart_tests W
  intro S _ t ht b p hp
  let _ := ht
  exact leftSmoothTripleAdd_of_sevenCharts W t b p hp

end FLT.Mazur.WeierstrassIntegralChart
